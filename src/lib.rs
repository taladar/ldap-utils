#![deny(unknown_lints)]
#![deny(renamed_and_removed_lints)]
#![forbid(unsafe_code)]
#![deny(deprecated)]
#![forbid(private_in_public)]
#![forbid(non_fmt_panics)]
#![deny(unreachable_code)]
#![deny(unreachable_patterns)]
#![forbid(unused_doc_comments)]
#![forbid(unused_must_use)]
#![deny(while_true)]
#![deny(unused_parens)]
#![deny(redundant_semicolons)]
#![deny(non_ascii_idents)]
#![deny(confusable_idents)]
#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]
#![warn(clippy::cargo_common_metadata)]
#![warn(rustdoc::missing_crate_level_docs)]
#![deny(rustdoc::broken_intra_doc_links)]
#![warn(missing_debug_implementations)]
#![deny(clippy::mod_module_files)]
#![doc = include_str!("../README.md")]

use chumsky::Parser;
use ldap_types::basic::RootDSE;
use ldap_types::schema::{
    attribute_type_parser, ldap_syntax_parser, matching_rule_parser, matching_rule_use_parser,
    object_class_parser, AttributeType, LDAPSchema, LDAPSyntax, MatchingRule, MatchingRuleUse,
    ObjectClass,
};

use ldap3::exop::{WhoAmI, WhoAmIResp};
use ldap3::result::SearchResult;
use ldap3::{Ldap, LdapConnAsync, LdapConnSettings, Scope, SearchEntry};
use native_tls::{Certificate, Identity, TlsConnector};

use std::fmt::Debug;
use std::fmt::Display;

use openssl::pkcs12::Pkcs12;
use openssl::pkey::PKey;
use openssl::x509::X509;

use std::fs::File;
use std::io::Read;
use std::path::Path;

use regex::Regex;

use dirs::home_dir;

use tracing::instrument;

use derive_builder::Builder;

use serde::Deserialize;

use std::convert::TryInto;

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};

use thiserror::Error;

/// creates a noop_control object for use with ldap3
///
/// the noop_control is supposed to perform the same operation
/// and return the same errors as the real operation but not make
/// any changes to the directory
///
/// OpenLDAP's implementation seems to be buggy, in my tests some uses of the
/// NOOP control lead to problems displaying affected objects until the LDAP
/// server was restarted
pub fn noop_control() -> ldap3::controls::RawControl {
    ldap3::controls::RawControl {
        ctype: "1.3.6.1.4.1.4203.666.5.2".to_string(),
        crit: true,
        val: None,
    }
}

/// error which can occur while parsing a scope
#[derive(Debug, Clone, Error)]
pub enum ScopeParserError {
    /// could not parse the value as a scope
    #[error("Could not parse {0} as an ldap scope")]
    CouldNotParseAsScope(String),
}

/// parse an [ldap3::Scope] from the string one would specify to use the same
/// scope with OpenLDAP's ldapsearch -s parameter
pub fn parse_scope(src: &str) -> Result<ldap3::Scope, ScopeParserError> {
    match src {
        "base" => Ok(ldap3::Scope::Base),
        "one" => Ok(ldap3::Scope::OneLevel),
        "sub" => Ok(ldap3::Scope::Subtree),
        s => Err(ScopeParserError::CouldNotParseAsScope(s.to_string())),
    }
}

/// a set of parameters for connecting to an LDAP server, including client-side
/// certificate auth support
#[derive(Debug, Builder, Deserialize)]
pub struct ConnectParameters {
    /// CA certificate path
    ca_cert_path: std::string::String,
    /// client certificate path
    client_cert_path: std::string::String,
    /// client key path
    client_key_path: std::string::String,
    /// the LDAP URL to connect to
    pub url: std::string::String,
}

/// errors which can happen when trying to retrieve connect parameters from openldap config
#[derive(Debug, Error)]
pub enum OpenLdapConnectParameterError {
    /// an error when compiling or using a regular expression
    #[error("regex error: {0}")]
    RegexError(#[from] regex::Error),
    /// an I/O error
    #[error("I/O error: {0}")]
    IOError(#[from] std::io::Error),
}

/// try to detect OpenLDAP connect parameters from its config files
/// (ldap.conf in /etc/ldap or /etc/openldap and .ldaprc in the user home dir)
#[instrument(skip(builder))]
pub fn openldap_connect_parameters(
    builder: &mut ConnectParametersBuilder,
) -> Result<&mut ConnectParametersBuilder, OpenLdapConnectParameterError> {
    let ldap_rc_content;
    let ldap_conf_content;
    if let Some(d) = home_dir() {
        let mut ldap_rc_filename = d;
        ldap_rc_filename.push(".ldaprc");
        if ldap_rc_filename.exists() {
            tracing::debug!("Using .ldaprc at {:?}", ldap_rc_filename);
            ldap_rc_content = std::fs::read_to_string(ldap_rc_filename)?;

            for line in ldap_rc_content.lines() {
                let ca_cert_re = Regex::new(r"^TLS_CACERT *(.*)$")?;
                if let Some(caps) = ca_cert_re.captures(line) {
                    let ca_cert_path = caps.get(1).unwrap().as_str();
                    tracing::debug!("Extracted .ldaprc TLS_CACERT value {}", ca_cert_path);
                    builder.ca_cert_path(ca_cert_path.to_string());
                }

                let client_cert_re = Regex::new(r"^TLS_CERT *(.*)$")?;
                if let Some(caps) = client_cert_re.captures(line) {
                    let client_cert_path = caps.get(1).unwrap().as_str();
                    tracing::debug!("Extracted .ldaprc TLS_CERT value {}", client_cert_path);
                    builder.client_cert_path(client_cert_path.to_string());
                }

                let client_key_re = Regex::new(r"^TLS_KEY *(.*)$")?;
                if let Some(caps) = client_key_re.captures(line) {
                    let client_key_path = caps.get(1).unwrap().as_str();
                    tracing::debug!("Extracted .ldaprc TLS_KEY value {}", client_key_path);
                    builder.client_key_path(client_key_path.to_string());
                }
            }
        }

        let mut ldap_conf_filename = Path::new("/etc/ldap/ldap.conf");
        if !ldap_conf_filename.exists() {
            ldap_conf_filename = Path::new("/etc/openldap/ldap.conf");
        }
        if ldap_conf_filename.exists() {
            tracing::debug!("Using ldap.conf at {:?}", ldap_conf_filename);
            ldap_conf_content = std::fs::read_to_string(ldap_conf_filename)?;

            for line in ldap_conf_content.lines() {
                let uri_re = Regex::new(r"^URI *(.*)$")?;
                if let Some(caps) = uri_re.captures(line) {
                    let url = caps.get(1).unwrap().as_str();
                    tracing::debug!("Extracted ldap.conf URI value {}", url);
                    builder.url(url.to_string());
                }
            }
        }
    }
    Ok(builder)
}

/// fill the builder with hardcoded default parameters
///
/// there is no default parameter for the URL
#[instrument(skip(builder))]
pub fn default_connect_parameters(
    builder: &mut ConnectParametersBuilder,
) -> &mut ConnectParametersBuilder {
    if builder.ca_cert_path.is_none() {
        builder.ca_cert_path("ca.crt".to_string());
    }
    if builder.client_cert_path.is_none() {
        builder.client_cert_path("client.crt".to_string());
    }
    if builder.client_key_path.is_none() {
        builder.client_key_path("client.key".to_string());
    }
    builder
}

/// error which can happen while reading connect parameters from a file
#[derive(Debug, Error)]
pub enum TomlConfigError {
    /// an I/O error
    #[error("I/O error: {0}")]
    IOError(#[from] std::io::Error),
    /// an error deserializing the TOML file
    #[error("Toml deserialization error: {0}")]
    TomlError(#[from] toml::de::Error),
}

/// load ldap connect parameters from a toml file
#[instrument]
pub fn toml_connect_parameters(
    filename: std::path::PathBuf,
) -> Result<ConnectParameters, TomlConfigError> {
    let config = std::fs::read_to_string(filename)?;
    let result: ConnectParameters = toml::from_str(&config)?;

    Ok(result)
}

/// errors which can happen when connecting to an LDAP server
#[derive(Debug, Error)]
pub enum ConnectError {
    /// an error when building the parameters, most likely a value
    /// that could not be retrieved from any config source
    #[error("Parameters builder error: {0}")]
    ParametersBuilderError(#[from] ConnectParametersBuilderError),
    /// an error when trying to retrieve connect parameters from OpenLDAP config files
    #[error("Error retrieving OpenLDAP connect parameters: {0}")]
    OpenLdapConnectParameterError(#[from] OpenLdapConnectParameterError),
    /// an I/O error
    #[error("I/O error: {0}")]
    IOError(#[from] std::io::Error),
    /// an error in the native_tls crate
    #[error("Native TLS error: {0}")]
    NativeTLSError(#[from] native_tls::Error),
    /// an error in the ldap3 crate
    #[error("ldap3 Ldap error: {0}")]
    LdapError(#[from] ldap3::LdapError),
    /// an error when compiling or using a regular expression
    #[error("regex error: {0}")]
    RegexError(#[from] regex::Error),
    /// an error in the openssl library used to read certificates and keys
    #[error("openssl error: {0}")]
    OpenSSLError(#[from] openssl::error::ErrorStack),
}

/// try to connect to an LDAP server using ldap3 using the OpenLDAP config files
/// supplemented by hardcoded default values
#[instrument]
pub async fn connect() -> Result<(Ldap, std::string::String), ConnectError> {
    let mut builder = ConnectParametersBuilder::default();
    openldap_connect_parameters(&mut builder)?;
    match builder.build() {
        Ok(result) => connect_with_parameters(result).await,
        Err(err_msg) => {
            tracing::error!(
                "Building of ConnectParameters based on OpenLDAP config files failed: {}",
                err_msg
            );
            let builder = default_connect_parameters(&mut builder);
            match builder.build() {
                Ok(result) => connect_with_parameters(result).await,
                Err(err) => {
                    tracing::error!("Building of ConnectParameters based on OpenLDAP config files and substituting default values for missing values failed: {}", err);
                    Err(ConnectError::ParametersBuilderError(err))
                }
            }
        }
    }
}

/// connect to an LDAP server using ldap3 with the given set of default parameters
#[instrument]
pub async fn connect_with_parameters(
    connect_parameters: ConnectParameters,
) -> Result<(Ldap, std::string::String), ConnectError> {
    let mut client_cert_contents = Vec::new();
    {
        let mut file = File::open(connect_parameters.client_cert_path)?;
        file.read_to_end(&mut client_cert_contents)?;
    }
    let client_cert = X509::from_pem(&client_cert_contents)?;
    let mut client_key_contents = Vec::new();
    {
        let mut file = File::open(connect_parameters.client_key_path)?;
        file.read_to_end(&mut client_key_contents)?;
    }
    let client_key = PKey::private_key_from_pem(&client_key_contents)?;
    let p12_password = "client";
    let p12 = Pkcs12::builder().build(p12_password, "client", &client_key, &client_cert)?;
    let p12_contents = p12.to_der()?;
    let mut ca_cert_contents = Vec::new();
    {
        let mut file = File::open(connect_parameters.ca_cert_path)?;
        file.read_to_end(&mut ca_cert_contents)?;
    }
    let identity = Identity::from_pkcs12(&p12_contents, p12_password)?;
    let ca_certificate = Certificate::from_pem(&ca_cert_contents)?;
    let connector = TlsConnector::builder()
        .identity(identity)
        .add_root_certificate(ca_certificate)
        .build()?;
    let ldap_settings = LdapConnSettings::new().set_connector(connector);
    let (ldap_conn_async, mut ldap) =
        LdapConnAsync::with_settings(ldap_settings, &connect_parameters.url.clone()).await?;
    ldap3::drive!(ldap_conn_async);
    ldap.sasl_external_bind().await?;
    let (exop, _res) = ldap.extended(WhoAmI).await?.success()?;
    let who_am_i: WhoAmIResp = exop.parse();
    let re = Regex::new(r"^.*,ou=[a-z]+,")?;
    let base_dn = re.replace_all(&who_am_i.authzid, "").to_string();
    Ok((ldap, base_dn))
}

/// an error during normal ldap operations (search, add, modify, update, delete,...)
#[derive(Debug, Error)]
pub enum LdapOperationError {
    /// an error in the ldap3 library
    #[error("ldap3 Ldap error: {0}")]
    LdapError(#[from] ldap3::LdapError),
    /// and error parsing an OID
    #[error("OID error: {0}")]
    OIDError(#[from] OIDError),
}

/// perform an LDAP search via ldap3, logging a proper error message if it fails
/// and returning an iterator to already unwrapped search entries
pub async fn ldap_search<'a, S: AsRef<str> + Clone + Display + Debug + Send + Sync>(
    ldap: &mut Ldap,
    base: &str,
    scope: Scope,
    filter: &str,
    attrs: Vec<S>,
) -> Result<Box<dyn Iterator<Item = SearchEntry> + 'a>, LdapOperationError> {
    let search_result = ldap.search(base, scope, filter, attrs.clone()).await?;
    let SearchResult(_rs, res) = &search_result;
    if res.rc != 0 {
        tracing::error!(
            "Error in LDAP query\n  base: {}\n  scope: {:?}\n  filter: {}\n  attrs: {:#?}",
            base,
            scope,
            filter,
            attrs
        );
        tracing::error!(
            "ldapsearch -Q -LLL -o ldif-wrap=no -b '{}' -s {} '{}' {}",
            base,
            format!("{:?}", scope).to_lowercase(),
            filter,
            itertools::join(attrs.iter(), " ")
        );
    }
    let (rs, _res) = search_result.success()?;
    Ok(Box::new(rs.into_iter().map(SearchEntry::construct)))
}

/// an error type in case parsing an OID fails when querying the RootDSE from ldap3
/// during the parsing of supported controls, extensions and features
#[derive(Debug)]
pub struct OIDError(oid::ObjectIdentifierError);

impl Display for OIDError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Error parsing OID: {:?}", self.0)
    }
}

impl std::error::Error for OIDError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

/// retrieve the [RootDSE] from an LDAP server using ldap3
#[instrument(skip(ldap))]
pub async fn query_root_dse(ldap: &mut Ldap) -> Result<Option<RootDSE>, LdapOperationError> {
    let mut it = ldap_search(
        ldap,
        "",
        Scope::Base,
        "(objectClass=*)",
        vec![
            "supportedLDAPVersion",
            "supportedControl",
            "supportedExtension",
            "supportedFeatures",
            "supportedSASLMechanisms",
            "configContext",
            "namingContexts",
            "subschemaSubentry",
        ],
    )
    .await?;
    if let Some(entry) = it.next() {
        let supported_ldap_version = entry
            .attrs
            .get("supportedLDAPVersion")
            .unwrap()
            .first()
            .unwrap();
        let supported_controls = entry.attrs.get("supportedControl").unwrap();
        let supported_extensions = entry.attrs.get("supportedExtension").unwrap();
        let supported_features = entry.attrs.get("supportedFeatures").unwrap();
        let supported_sasl_mechanisms = entry.attrs.get("supportedSASLMechanisms").unwrap();
        let config_context = entry.attrs.get("configContext").unwrap().first().unwrap();
        let naming_contexts = entry.attrs.get("namingContexts").unwrap();
        let subschema_subentry = entry
            .attrs
            .get("subschemaSubentry")
            .unwrap()
            .first()
            .unwrap();
        return Ok(Some(RootDSE {
            supported_ldap_version: supported_ldap_version.to_string(),
            supported_controls: supported_controls
                .iter()
                .map(|x| x.clone().try_into())
                .collect::<Result<_, _>>()
                .map_err(OIDError)?,
            supported_extensions: supported_extensions
                .iter()
                .map(|x| x.clone().try_into())
                .collect::<Result<_, _>>()
                .map_err(OIDError)?,
            supported_features: supported_features
                .iter()
                .map(|x| x.clone().try_into())
                .collect::<Result<_, _>>()
                .map_err(OIDError)?,
            supported_sasl_mechanisms: supported_sasl_mechanisms.to_vec(),
            config_context: config_context.to_string(),
            naming_contexts: naming_contexts.to_vec(),
            subschema_subentry: subschema_subentry.to_string(),
        }));
    }
    Ok(None)
}

/// a wrapped error in case parsing fails when retrieving the [LDAPSchema]
/// from an ldap3 server.
#[derive(Debug)]
pub struct ChumskyError(Vec<chumsky::error::Simple<char>>);

impl Display for ChumskyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Parse error: {:?}", self.0)
    }
}

impl std::error::Error for ChumskyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

/// print chumsky parse errors using ariadne
#[instrument]
pub fn print_errors(src: &str, errs: &[chumsky::error::Simple<char>]) {
    errs.iter().for_each(|e| {
        let msg = format!(
            "{}{}, expected {}",
            if e.found().is_some() {
                "Unexpected token"
            } else {
                "Unexpected end of input"
            },
            if let Some(label) = e.label() {
                format!(" while parsing {}", label)
            } else {
                String::new()
            },
            if e.expected().len() == 0 {
                "end of input".to_string()
            } else {
                e.expected()
                    .map(|expected| match expected {
                        Some(expected) => expected.to_string(),
                        None => "end of input".to_string(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            },
        );

        let report = Report::build(ReportKind::Error, (), e.span().start)
            .with_code(3)
            .with_message(msg)
            .with_label(
                Label::new(e.span())
                    .with_message(format!(
                        "Unexpected {}",
                        e.found()
                            .map(|c| format!("token {}", c.fg(Color::Red)))
                            .unwrap_or_else(|| "end of input".to_string())
                    ))
                    .with_color(Color::Red),
            );

        let report = match e.reason() {
            chumsky::error::SimpleReason::Unclosed { span, delimiter } => report.with_label(
                Label::new(span.clone())
                    .with_message(format!(
                        "Unclosed delimiter {}",
                        delimiter.fg(Color::Yellow)
                    ))
                    .with_color(Color::Yellow),
            ),
            chumsky::error::SimpleReason::Unexpected => report,
            chumsky::error::SimpleReason::Custom(msg) => report.with_label(
                Label::new(e.span())
                    .with_message(format!("{}", msg.fg(Color::Yellow)))
                    .with_color(Color::Yellow),
            ),
        };

        report.finish().print(Source::from(&src)).unwrap();
    });
}

/// error which can happen while retrieving and parsing the LDAP schema
#[derive(Debug, Error)]
pub enum LdapSchemaError {
    /// an error in the ldap operations performed while retrieving the schema
    #[error("Ldap operation error: {0}")]
    LdapOperationError(#[from] LdapOperationError),
    /// an error while parsing the retrieved schema
    #[error("chumsky parser error: {0}")]
    ChumskyError(#[from] ChumskyError),
}

/// Retrieve the LDAP schema from an LDAP server using ldap3
///
/// tested with OpenLDAP
#[instrument(skip(ldap))]
pub async fn query_ldap_schema(ldap: &mut Ldap) -> Result<Option<LDAPSchema>, LdapSchemaError> {
    if let Some(root_dse) = query_root_dse(ldap).await? {
        let mut it = ldap_search(
            ldap,
            &root_dse.subschema_subentry,
            Scope::Base,
            "(objectClass=*)",
            vec![
                "ldapSyntaxes",
                "matchingRules",
                "matchingRuleUse",
                "attributeTypes",
                "objectClasses",
            ],
        )
        .await?;

        if let Some(entry) = it.next() {
            let ldap_syntaxes = entry
                .attrs
                .get("ldapSyntaxes")
                .unwrap()
                .iter()
                .map(|x| match ldap_syntax_parser().parse_recovery(x.as_str()) {
                    (Some(ldap_syntax), _) => Ok(ldap_syntax),
                    (_, errs) => {
                        print_errors(x, &errs);
                        Err(ChumskyError(errs))
                    }
                })
                .collect::<Result<Vec<LDAPSyntax>, ChumskyError>>()?;
            let matching_rules = entry
                .attrs
                .get("matchingRules")
                .unwrap()
                .iter()
                .map(
                    |x| match matching_rule_parser().parse_recovery(x.as_str()) {
                        (Some(matching_rule), _) => Ok(matching_rule),
                        (_, errs) => {
                            print_errors(x, &errs);
                            Err(ChumskyError(errs))
                        }
                    },
                )
                .collect::<Result<Vec<MatchingRule>, ChumskyError>>()?;
            let matching_rule_use = entry
                .attrs
                .get("matchingRuleUse")
                .unwrap()
                .iter()
                .map(
                    |x| match matching_rule_use_parser().parse_recovery(x.as_str()) {
                        (Some(matching_rule_use), _) => Ok(matching_rule_use),
                        (_, errs) => {
                            print_errors(x, &errs);
                            Err(ChumskyError(errs))
                        }
                    },
                )
                .collect::<Result<Vec<MatchingRuleUse>, ChumskyError>>()?;
            let attribute_types = entry
                .attrs
                .get("attributeTypes")
                .unwrap()
                .iter()
                .map(
                    |x| match attribute_type_parser().parse_recovery(x.as_str()) {
                        (Some(attribute_type), _) => Ok(attribute_type),
                        (_, errs) => {
                            print_errors(x, &errs);
                            Err(ChumskyError(errs))
                        }
                    },
                )
                .collect::<Result<Vec<AttributeType>, ChumskyError>>()?;
            let object_classes = entry
                .attrs
                .get("objectClasses")
                .unwrap()
                .iter()
                .map(|x| match object_class_parser().parse_recovery(x.as_str()) {
                    (Some(object_class), _) => Ok(object_class),
                    (_, errs) => {
                        print_errors(x, &errs);
                        Err(ChumskyError(errs))
                    }
                })
                .collect::<Result<Vec<ObjectClass>, ChumskyError>>()?;
            return Ok(Some(LDAPSchema {
                ldap_syntaxes,
                matching_rules,
                matching_rule_use,
                attribute_types,
                object_classes,
            }));
        }
    }
    Ok(None)
}

/// check if an [ldap3::LdapResult] is either a success or the success code returned by an operation using the [noop_control]
pub fn success_or_noop_success(
    ldap_result: ldap3::LdapResult,
) -> ldap3::result::Result<ldap3::LdapResult> {
    // 16654 is success in the presence of the noop control https://ldap.com/ldap-result-code-reference-other-server-side-result-codes/#rc-noOperation
    if ldap_result.rc == 0 || ldap_result.rc == 16654 {
        Ok(ldap_result)
    } else {
        Err(ldap3::LdapError::from(ldap_result))
    }
}

/// delete an LDAP entry recursively using ldap3
#[instrument(skip(ldap))]
pub async fn delete_recursive(
    ldap: &mut Ldap,
    dn: &str,
    controls: Vec<ldap3::controls::RawControl>,
) -> Result<(), LdapOperationError> {
    tracing::debug!("Deleting {} recursively", dn);
    let it = ldap_search(
        ldap,
        dn,
        Scope::Subtree,
        "(objectClass=*)",
        Vec::<String>::new(),
    )
    .await?;
    let mut entries = vec![];
    for entry in it {
        tracing::debug!("Found child entry to delete {}", entry.dn);
        entries.push(entry.dn);
    }
    entries.sort_by_key(|b| std::cmp::Reverse(b.len()));
    for dn in entries {
        tracing::debug!("Deleting child entry {}", dn);
        success_or_noop_success(ldap.with_controls(controls.to_owned()).delete(&dn).await?)?;
    }
    Ok(())
}
