#![doc = include_str!("../README.md")]

use diff::{Diff, VecDiffType};

use chumsky::Parser as _;
use ldap_types::basic::{ChumskyError, LDAPEntry, LDAPOperation, OIDWithLength, RootDSE};
use ldap_types::schema::{
    AttributeType, LDAPSchema, LDAPSyntax, MatchingRule, MatchingRuleUse, ObjectClass,
    attribute_type_parser, ldap_syntax_parser, matching_rule_parser, matching_rule_use_parser,
    object_class_parser,
};

use ldap3::exop::{WhoAmI, WhoAmIResp};
use ldap3::{Ldap, LdapConnAsync, LdapConnSettings, Scope, SearchEntry};
use native_tls::{Certificate, Identity, TlsConnector};
use oid::ObjectIdentifier;

use std::sync::LazyLock;

/// Object Identifier for the DN syntax, as defined in RFC 4517.
pub static DN_SYNTAX_OID: LazyLock<Result<OIDWithLength, oid::ObjectIdentifierError>> =
    LazyLock::new(|| {
        Ok(OIDWithLength {
            oid: ObjectIdentifier::try_from("1.3.6.1.4.1.1466.115.121.1.12")?,
            length: None,
        })
    });

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Write as _;

use openssl::pkcs12::Pkcs12;
use openssl::pkey::PKey;
use openssl::x509::X509;

use std::fs::File;
use std::io::Read as _;
use std::path::Path;

use regex::Regex;

use dirs2::home_dir;

use tracing::instrument;

use derive_builder::Builder;

use serde::Deserialize;

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
#[must_use]
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
///
/// # Errors
///
/// fails if the scope is not one of the expected values
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
#[derive(Debug, Clone, Builder, Deserialize)]
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
///
/// # Errors
///
/// fails if reading or parsing OpenLDAP config fails
#[instrument(skip(builder))]
pub fn openldap_connect_parameters(
    builder: &mut ConnectParametersBuilder,
) -> Result<&mut ConnectParametersBuilder, OpenLdapConnectParameterError> {
    let ldap_rc_content;
    let ldap_conf_content;
    if let Some(d) = home_dir() {
        let ldap_rc_filename = d.join(".ldaprc");
        if ldap_rc_filename.exists() {
            tracing::debug!("Using .ldaprc at {:?}", ldap_rc_filename);
            ldap_rc_content = fs_err::read_to_string(ldap_rc_filename)?;

            let ca_cert_re = Regex::new(r"^TLS_CACERT *(.*)$")?;
            let client_cert_re = Regex::new(r"^TLS_CERT *(.*)$")?;
            let client_key_re = Regex::new(r"^TLS_KEY *(.*)$")?;
            for line in ldap_rc_content.lines() {
                if let Some(ca_cert_path) = ca_cert_re
                    .captures(line)
                    .and_then(|caps| caps.get(1))
                    .map(|m| m.as_str())
                {
                    tracing::debug!("Extracted .ldaprc TLS_CACERT value {}", ca_cert_path);
                    builder.ca_cert_path(ca_cert_path.to_string());
                }

                if let Some(client_cert_path) = client_cert_re
                    .captures(line)
                    .and_then(|caps| caps.get(1))
                    .map(|m| m.as_str())
                {
                    tracing::debug!("Extracted .ldaprc TLS_CERT value {}", client_cert_path);
                    builder.client_cert_path(client_cert_path.to_string());
                }

                if let Some(client_key_path) = client_key_re
                    .captures(line)
                    .and_then(|caps| caps.get(1))
                    .map(|m| m.as_str())
                {
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
            ldap_conf_content = fs_err::read_to_string(ldap_conf_filename)?;

            let uri_re = Regex::new(r"^URI *(.*)$")?;
            for line in ldap_conf_content.lines() {
                if let Some(url) = uri_re
                    .captures(line)
                    .and_then(|caps| caps.get(1))
                    .map(|m| m.as_str())
                {
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
///
/// # Errors
///
/// fails if reading or parsing the toml config fails
#[instrument]
pub fn toml_connect_parameters(
    filename: std::path::PathBuf,
) -> Result<ConnectParameters, TomlConfigError> {
    let config = fs_err::read_to_string(filename)?;
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
///
/// # Errors
///
/// fails if OpenLDAP config could not be read or parsed or if the connection
/// attempt with those parameters fails
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
                    tracing::error!(
                        "Building of ConnectParameters based on OpenLDAP config files and substituting default values for missing values failed: {}",
                        err
                    );
                    Err(ConnectError::ParametersBuilderError(err))
                }
            }
        }
    }
}

/// connect to an LDAP server using ldap3 with the given set of default parameters
///
/// # Errors
///
/// fails if reading or parsing of client certificates fails or if the
/// actual connection attempt fails
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
    let p12 = Pkcs12::builder()
        .name("client")
        .pkey(&client_key)
        .cert(&client_cert)
        .build2(p12_password)?;
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
    /// An expected attribute was missing from the LDAP entry.
    #[error("Missing expected attribute: {0}")]
    MissingAttribute(String),
    /// an LDAP operation failed, with the details of the operation needed
    /// to understand and reproduce the failure
    #[error("{operation} failed: {}", describe_ldap3_error(.operation, .source))]
    OperationFailed {
        /// the operation that failed
        operation: Box<FailedLdapOperation>,
        /// the error returned by ldap3
        #[source]
        source: ldap3::LdapError,
    },
}

impl LdapOperationError {
    /// if this error is a noSuchObject (rc=32) result of an LDAP operation
    /// this returns the classification of which part of the requested DN
    /// is missing
    #[must_use]
    pub fn no_such_object(&self) -> Option<NoSuchObject> {
        match self {
            Self::OperationFailed {
                operation,
                source: ldap3::LdapError::LdapResult { result },
            } if result.rc == LDAP_RC_NO_SUCH_OBJECT => {
                Some(NoSuchObject::classify(operation.dn(), &result.matched))
            }
            Self::LdapError(_)
            | Self::OIDError(_)
            | Self::MissingAttribute(_)
            | Self::OperationFailed { .. } => None,
        }
    }

    /// the LDAP operation that failed, if this error is the result of a
    /// failed LDAP operation
    #[must_use]
    pub const fn operation(&self) -> Option<&FailedLdapOperation> {
        match self {
            Self::OperationFailed { operation, .. } => Some(operation),
            Self::LdapError(_) | Self::OIDError(_) | Self::MissingAttribute(_) => None,
        }
    }
}

/// the LDAP result code for noSuchObject
const LDAP_RC_NO_SUCH_OBJECT: u32 = 32;

/// an LDAP operation that failed, with the parameters needed to understand
/// and reproduce the failure
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum FailedLdapOperation {
    /// an LDAP search
    Search {
        /// the search base DN
        base: String,
        /// the search scope
        scope: Scope,
        /// the search filter
        filter: String,
        /// the requested attributes
        attrs: Vec<String>,
    },
    /// adding an LDAP entry
    Add {
        /// the DN of the entry to add
        dn: String,
    },
    /// modifying an LDAP entry
    Modify {
        /// the DN of the entry to modify
        dn: String,
    },
    /// deleting an LDAP entry
    Delete {
        /// the DN of the entry to delete
        dn: String,
    },
}

impl FailedLdapOperation {
    /// the DN the operation was performed on (the base DN for searches)
    #[must_use]
    pub fn dn(&self) -> &str {
        match self {
            Self::Search { base, .. } => base,
            Self::Add { dn } | Self::Modify { dn } | Self::Delete { dn } => dn,
        }
    }

    /// an ldapsearch command line that performs the same search, for
    /// reproducing a failed search manually
    #[must_use]
    pub fn ldapsearch_command(&self) -> Option<String> {
        match self {
            Self::Search {
                base,
                scope,
                filter,
                attrs,
            } => Some(format!(
                "ldapsearch -Q -LLL -o ldif-wrap=no -b '{}' -s {} '{}' {}",
                base,
                ldapsearch_scope_name(*scope),
                filter,
                itertools::join(attrs.iter(), " ")
            )),
            Self::Add { .. } | Self::Modify { .. } | Self::Delete { .. } => None,
        }
    }
}

impl Display for FailedLdapOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Search {
                base,
                scope,
                filter,
                attrs,
            } => write!(
                f,
                "LDAP search (base: '{}', scope: {}, filter: '{}', attributes: {})",
                base,
                ldapsearch_scope_name(*scope),
                filter,
                if attrs.is_empty() {
                    "all".to_string()
                } else {
                    itertools::join(attrs.iter(), " ")
                }
            ),
            Self::Add { dn } => write!(f, "LDAP add of '{dn}'"),
            Self::Modify { dn } => write!(f, "LDAP modify of '{dn}'"),
            Self::Delete { dn } => write!(f, "LDAP delete of '{dn}'"),
        }
    }
}

/// the name of a search scope as used by the -s option of ldapsearch
const fn ldapsearch_scope_name(scope: Scope) -> &'static str {
    match scope {
        Scope::Base => "base",
        Scope::OneLevel => "one",
        Scope::Subtree => "sub",
    }
}

/// the name of an LDAP result code as defined in RFC 4511 (and some common
/// extensions)
const fn ldap_result_code_name(rc: u32) -> &'static str {
    match rc {
        0 => "success",
        1 => "operationsError",
        2 => "protocolError",
        3 => "timeLimitExceeded",
        4 => "sizeLimitExceeded",
        5 => "compareFalse",
        6 => "compareTrue",
        7 => "authMethodNotSupported",
        8 => "strongerAuthRequired",
        10 => "referral",
        11 => "adminLimitExceeded",
        12 => "unavailableCriticalExtension",
        13 => "confidentialityRequired",
        14 => "saslBindInProgress",
        16 => "noSuchAttribute",
        17 => "undefinedAttributeType",
        18 => "inappropriateMatching",
        19 => "constraintViolation",
        20 => "attributeOrValueExists",
        21 => "invalidAttributeSyntax",
        32 => "noSuchObject",
        33 => "aliasProblem",
        34 => "invalidDNSyntax",
        36 => "aliasDereferencingProblem",
        48 => "inappropriateAuthentication",
        49 => "invalidCredentials",
        50 => "insufficientAccessRights",
        51 => "busy",
        52 => "unavailable",
        53 => "unwillingToPerform",
        54 => "loopDetect",
        64 => "namingViolation",
        65 => "objectClassViolation",
        66 => "notAllowedOnNonLeaf",
        67 => "notAllowedOnRDN",
        68 => "entryAlreadyExists",
        69 => "objectClassModsProhibited",
        71 => "affectsMultipleDSAs",
        80 => "other",
        88 => "abandoned",
        122 => "assertionFailed",
        16654 => "noOperation",
        _ => "unknown",
    }
}

/// describe an error returned by ldap3 for a given operation in a way that
/// helps with finding the cause
fn describe_ldap3_error(operation: &FailedLdapOperation, error: &ldap3::LdapError) -> String {
    match error {
        ldap3::LdapError::LdapResult { result } => {
            let mut description = if result.rc == LDAP_RC_NO_SUCH_OBJECT {
                NoSuchObject::classify(operation.dn(), &result.matched).to_string()
            } else {
                let mut description =
                    format!("rc={} ({})", result.rc, ldap_result_code_name(result.rc));
                if !result.matched.is_empty() {
                    write!(description, " (matched DN: '{}')", result.matched).ok();
                }
                description
            };
            if !result.text.is_empty() {
                write!(description, ", server message: {}", result.text).ok();
            }
            if let Some(cmd) = operation.ldapsearch_command() {
                write!(description, "\n  to reproduce: {cmd}").ok();
            }
            description
        }
        e => e.to_string(),
    }
}

/// which part of a requested DN does not exist, determined from a
/// noSuchObject result and the matched DN returned by the server
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum NoSuchObjectKind {
    /// the requested entry itself does not exist, its parent does
    EntryMissing,
    /// an ancestor of the requested entry does not exist
    AncestorMissing {
        /// the highest missing ancestor, the one directly below the matched DN
        first_missing: String,
    },
    /// the server did not report any existing part of the DN, not even
    /// the base DN of the directory
    NothingMatched,
    /// the matched DN returned by the server is not an ancestor of the
    /// requested DN (or could not be compared to it)
    Unclassified,
}

/// the classification of a noSuchObject (rc=32) LDAP result
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NoSuchObject {
    /// the DN that was requested (the search base for searches)
    pub requested: String,
    /// the matched DN returned by the server, the deepest existing ancestor
    /// of the requested DN
    pub matched: String,
    /// which part of the requested DN is missing
    pub kind: NoSuchObjectKind,
}

impl NoSuchObject {
    /// classify a noSuchObject result based on the requested DN and the
    /// matched DN returned by the server
    #[must_use]
    pub fn classify(requested: &str, matched: &str) -> Self {
        let kind = if matched.trim().is_empty() {
            NoSuchObjectKind::NothingMatched
        } else {
            let requested_rdns = split_dn(requested);
            let matched_rdns = split_dn(matched);
            let missing_count = requested_rdns.len().saturating_sub(matched_rdns.len());
            let is_ancestor = missing_count > 0
                && requested_rdns
                    .iter()
                    .skip(missing_count)
                    .zip(matched_rdns.iter())
                    .all(|(r, m)| normalize_rdn(r) == normalize_rdn(m));
            if !is_ancestor {
                NoSuchObjectKind::Unclassified
            } else if missing_count == 1 {
                NoSuchObjectKind::EntryMissing
            } else {
                NoSuchObjectKind::AncestorMissing {
                    first_missing: itertools::join(
                        requested_rdns.iter().skip(missing_count.saturating_sub(1)),
                        ",",
                    ),
                }
            }
        };
        Self {
            requested: requested.to_string(),
            matched: matched.to_string(),
            kind,
        }
    }
}

impl Display for NoSuchObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            NoSuchObjectKind::EntryMissing => write!(
                f,
                "entry '{}' does not exist (noSuchObject, its parent '{}' does exist)",
                self.requested, self.matched
            ),
            NoSuchObjectKind::AncestorMissing { first_missing } => write!(
                f,
                "'{}' does not exist, so neither does '{}' (noSuchObject, deepest existing ancestor: '{}')",
                first_missing, self.requested, self.matched
            ),
            NoSuchObjectKind::NothingMatched => write!(
                f,
                "no part of '{}' exists on this server, not even the base of the directory (noSuchObject without matched DN); check the server and the base DN, entries hidden by access controls look the same",
                self.requested
            ),
            NoSuchObjectKind::Unclassified => write!(
                f,
                "'{}' does not exist (noSuchObject, matched DN reported by the server: '{}')",
                self.requested, self.matched
            ),
        }
    }
}

/// split a DN string into its RDN strings on unescaped commas, trimming
/// whitespace around each RDN
fn split_dn(dn: &str) -> Vec<&str> {
    let mut rdns = Vec::new();
    let mut start = 0;
    let mut escaped = false;
    for (i, c) in dn.char_indices() {
        if escaped {
            escaped = false;
        } else if c == '\\' {
            escaped = true;
        } else if c == ',' {
            if let Some(rdn) = dn.get(start..i) {
                rdns.push(rdn.trim());
            }
            start = i.saturating_add(1);
        }
    }
    if let Some(rdn) = dn.get(start..) {
        let rdn = rdn.trim();
        if !rdn.is_empty() || !rdns.is_empty() {
            rdns.push(rdn);
        }
    }
    rdns
}

/// normalize an RDN string for comparison, ignoring case and whitespace
/// around the = and + separators
///
/// this is only meant for comparisons in error messages, it does not
/// implement the matching rules of the individual attributes
fn normalize_rdn(rdn: &str) -> String {
    rdn.split('+')
        .map(|ava| {
            ava.split_once('=').map_or_else(
                || ava.trim().to_lowercase(),
                |(k, v)| format!("{}={}", k.trim().to_lowercase(), v.trim().to_lowercase()),
            )
        })
        .collect::<Vec<_>>()
        .join("+")
}

/// perform an LDAP search via ldap3, returning an error that includes the
/// search parameters if it fails and returning an iterator to already
/// unwrapped search entries
///
/// # Errors
///
/// fails if the underlying ldap search operation fails or returns a non-success code
pub async fn ldap_search<'a, S: AsRef<str> + Clone + Display + Debug + Send + Sync>(
    ldap: &mut Ldap,
    base: &str,
    scope: Scope,
    filter: &str,
    attrs: Vec<S>,
) -> Result<Box<dyn Iterator<Item = SearchEntry> + 'a>, LdapOperationError> {
    let operation = || {
        Box::new(FailedLdapOperation::Search {
            base: base.to_string(),
            scope,
            filter: filter.to_string(),
            attrs: attrs.iter().map(ToString::to_string).collect(),
        })
    };
    let search_result = ldap
        .search(base, scope, filter, attrs.clone())
        .await
        .map_err(|source| LdapOperationError::OperationFailed {
            operation: operation(),
            source,
        })?;
    let (rs, _res) =
        search_result
            .success()
            .map_err(|source| LdapOperationError::OperationFailed {
                operation: operation(),
                source,
            })?;
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
///
/// # Errors
///
/// Returns `LdapOperationError` if the LDAP search fails, or if a required attribute
/// is missing from the RootDSE entry, or if an OID cannot be parsed.
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
            .ok_or(LdapOperationError::MissingAttribute(
                "supportedLDAPVersion".to_string(),
            ))?
            .first()
            .ok_or(LdapOperationError::MissingAttribute(
                "supportedLDAPVersion".to_string(),
            ))?;
        let supported_controls =
            entry
                .attrs
                .get("supportedControl")
                .ok_or(LdapOperationError::MissingAttribute(
                    "supportedControl".to_string(),
                ))?;
        let supported_extensions =
            entry
                .attrs
                .get("supportedExtension")
                .ok_or(LdapOperationError::MissingAttribute(
                    "supportedExtension".to_string(),
                ))?;
        let supported_features =
            entry
                .attrs
                .get("supportedFeatures")
                .ok_or(LdapOperationError::MissingAttribute(
                    "supportedFeatures".to_string(),
                ))?;
        let supported_sasl_mechanisms = entry.attrs.get("supportedSASLMechanisms").ok_or(
            LdapOperationError::MissingAttribute("supportedSASLMechanisms".to_string()),
        )?;
        let config_context = entry
            .attrs
            .get("configContext")
            .ok_or(LdapOperationError::MissingAttribute(
                "configContext".to_string(),
            ))?
            .first()
            .ok_or(LdapOperationError::MissingAttribute(
                "configContext".to_string(),
            ))?;
        let naming_contexts =
            entry
                .attrs
                .get("namingContexts")
                .ok_or(LdapOperationError::MissingAttribute(
                    "namingContexts".to_string(),
                ))?;
        let subschema_subentry = entry
            .attrs
            .get("subschemaSubentry")
            .ok_or(LdapOperationError::MissingAttribute(
                "subschemaSubentry".to_string(),
            ))?
            .first()
            .ok_or(LdapOperationError::MissingAttribute(
                "subschemaSubentry".to_string(),
            ))?;
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

/// error which can happen while retrieving and parsing the LDAP schema
#[derive(Debug, Error)]
pub enum LdapSchemaError {
    /// an error in the ldap operations performed while retrieving the schema
    #[error("Ldap operation error: {0}")]
    LdapOperationError(#[from] LdapOperationError),
    /// an error while parsing the retrieved schema
    #[error("chumsky parser error: {0}")]
    ChumskyError(#[from] ChumskyError<chumsky::error::Rich<'static, char>>),
}

/// Retrieve the LDAP schema from an LDAP server using ldap3
///
/// tested with OpenLDAP
///
/// # Errors
///
/// fails if the underlying ldap query or the parsing of the results of that query fail
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
                .ok_or(LdapOperationError::MissingAttribute(
                    "ldapSyntaxes".to_string(),
                ))?
                .iter()
                .map(|x| match ldap_syntax_parser().parse(x.as_str()).into_output_errors() {
                    (Some(ldap_syntax), _) => Ok(ldap_syntax),
                    (_, errs) => Err(ChumskyError {
                        description: "ldap syntax".to_string(),
                        source: x.to_string(),
                        errors: errs.into_iter().map(|e| e.into_owned()).collect(),
                    }),
                })
                .collect::<Result<Vec<LDAPSyntax>, ChumskyError<chumsky::error::Rich<'static, char>>>>()?;
            let matching_rules = entry
                .attrs
                .get("matchingRules")
                .ok_or(LdapOperationError::MissingAttribute(
                    "matchingRules".to_string(),
                ))?
                .iter()
                .map(
                    |x| match matching_rule_parser().parse(x.as_str()).into_output_errors() {
                        (Some(matching_rule), _) => Ok(matching_rule),
                        (_, errs) => Err(ChumskyError {
                            description: "matching rule".to_string(),
                            source: x.to_string(),
                            errors: errs.into_iter().map(|e| e.into_owned()).collect(),
                        }),
                    },
                )
                .collect::<Result<Vec<MatchingRule>, ChumskyError<chumsky::error::Rich<'static, char>>>>()?;
            let matching_rule_use =
                entry
                    .attrs
                    .get("matchingRuleUse")
                    .ok_or(LdapOperationError::MissingAttribute(
                        "matchingRuleUse".to_string(),
                    ))?
                    .iter()
                    .map(|x| {
                        match matching_rule_use_parser()
                            .parse(x.as_str())
                            .into_output_errors()
                        {
                            (Some(matching_rule_use), _) => Ok(matching_rule_use),
                            (_, errs) => Err(ChumskyError {
                                description: "matching rule use".to_string(),
                                source: x.to_string(),
                                errors: errs.into_iter().map(|e| e.into_owned()).collect(),
                            }),
                        }
                    })
                    .collect::<Result<
                        Vec<MatchingRuleUse>,
                        ChumskyError<chumsky::error::Rich<'static, char>>,
                    >>()?;
            let attribute_types = entry
                .attrs
                .get("attributeTypes")
                .ok_or(LdapOperationError::MissingAttribute(
                    "attributeTypes".to_string(),
                ))?
                .iter()
                .map(
                    |x| match attribute_type_parser().parse(x.as_str()).into_output_errors() {
                        (Some(attribute_type), _) => Ok(attribute_type),
                        (_, errs) => Err(ChumskyError {
                            description: "attribute type".to_string(),
                            source: x.to_string(),
                            errors: errs.into_iter().map(|e| e.into_owned()).collect(),
                        }),
                    },
                )
                .collect::<Result<Vec<AttributeType>, ChumskyError<chumsky::error::Rich<'static, char>>>>()?;
            let object_classes = entry
                .attrs
                .get("objectClasses")
                .ok_or(LdapOperationError::MissingAttribute(
                    "objectClasses".to_string(),
                ))?
                .iter()
                .map(|x| match object_class_parser().parse(x.as_str()).into_output_errors() {
                    (Some(object_class), _) => Ok(object_class),
                    (_, errs) => Err(ChumskyError {
                        description: "object class".to_string(),
                        source: x.to_string(),
                        errors: errs.into_iter().map(|e| e.into_owned()).collect(),
                    }),
                })
                .collect::<Result<Vec<ObjectClass>, ChumskyError<chumsky::error::Rich<'static, char>>>>()?;
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
///
/// # Errors
///
/// fails if the LDAP result code is neither of the success codes
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
///
/// # Errors
///
/// fails if the underlying individual delete operations fail
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
        let delete_failed = |source| LdapOperationError::OperationFailed {
            operation: Box::new(FailedLdapOperation::Delete { dn: dn.clone() }),
            source,
        };
        success_or_noop_success(
            ldap.with_controls(controls.to_owned())
                .delete(&dn)
                .await
                .map_err(delete_failed)?,
        )
        .map_err(delete_failed)?;
    }
    Ok(())
}

/// of the same modify operation because otherwise we might successfully apply the textual modifications
/// and then fail on the binary ones, leaving behind a half-modified object
pub fn mods_as_bin_mods<'a, T>(mods: T) -> Vec<ldap3::Mod<Vec<u8>>>
where
    T: IntoIterator<Item = &'a ldap3::Mod<String>>,
{
    let mut result: Vec<ldap3::Mod<Vec<u8>>> = vec![];
    for m in mods {
        match m {
            ldap3::Mod::Add(k, v) => {
                result.push(ldap3::Mod::Add(
                    k.as_bytes().to_vec(),
                    v.iter().map(|s| s.as_bytes().to_vec()).collect(),
                ));
            }
            ldap3::Mod::Delete(k, v) => {
                result.push(ldap3::Mod::Delete(
                    k.as_bytes().to_vec(),
                    v.iter().map(|s| s.as_bytes().to_vec()).collect(),
                ));
            }
            ldap3::Mod::Replace(k, v) => {
                result.push(ldap3::Mod::Replace(
                    k.as_bytes().to_vec(),
                    v.iter().map(|s| s.as_bytes().to_vec()).collect(),
                ));
            }
            ldap3::Mod::Increment(k, v) => {
                result.push(ldap3::Mod::Increment(
                    k.as_bytes().to_vec(),
                    v.as_bytes().to_vec(),
                ));
            }
        }
    }
    result
}

/// apply the LDAP operations on a given LDAP server.
///
/// The operations should not include the Base-DN in its internally stored DNs
/// It will be added automatically. This allows for easier generation of comparisons
/// between objects on two different LDAP servers with different base DNs.
///
/// # Errors
///
/// fails if the underlying individual ldap operations fail
#[instrument(skip(ldap, ldap_operations))]
pub async fn apply_ldap_operations(
    ldap: &mut Ldap,
    ldap_base_dn: &str,
    ldap_operations: &[LDAPOperation],
    controls: Vec<ldap3::controls::RawControl>,
) -> Result<(), LdapOperationError> {
    tracing::debug!(
        "The following operations use the LDAP controls: {:#?}",
        controls
    );
    for op in ldap_operations {
        match op {
            LDAPOperation::Add(LDAPEntry {
                dn,
                attrs,
                bin_attrs,
            }) => {
                let full_dn = format!("{dn},{ldap_base_dn}");
                tracing::debug!(
                    "Adding LDAP entry at {} with attributes\n{:#?}\nand binary attributes\n{:#?}",
                    &full_dn,
                    attrs,
                    bin_attrs
                );
                // we need to perform the add in one operation or we will run into problems with
                // objectclass requirements
                let mut combined_attrs: Vec<(Vec<u8>, HashSet<Vec<u8>>)> = bin_attrs
                    .iter()
                    .map(|(k, v)| {
                        (
                            k.to_owned().as_bytes().to_vec(),
                            v.iter().map(|s| s.to_owned()).collect::<HashSet<Vec<u8>>>(),
                        )
                    })
                    .collect();
                combined_attrs.extend(attrs.iter().map(|(k, v)| {
                    (
                        k.to_owned().as_bytes().to_vec(),
                        v.iter()
                            .map(|s| s.as_bytes().to_vec())
                            .collect::<HashSet<Vec<u8>>>(),
                    )
                }));
                let add_failed = |source| LdapOperationError::OperationFailed {
                    operation: Box::new(FailedLdapOperation::Add {
                        dn: full_dn.clone(),
                    }),
                    source,
                };
                ldap.with_controls(controls.to_owned())
                    .add(&full_dn, combined_attrs)
                    .await
                    .map_err(add_failed)?
                    .success()
                    .map_err(add_failed)?;
            }
            LDAPOperation::Delete { dn } => {
                let full_dn = format!("{dn},{ldap_base_dn}");
                tracing::debug!("Deleting LDAP entry at {}", &full_dn);
                delete_recursive(ldap, &full_dn, controls.to_owned()).await?;
            }
            LDAPOperation::Modify { dn, mods, bin_mods } => {
                let full_dn = format!("{dn},{ldap_base_dn}");
                tracing::debug!(
                    "Modifying LDAP entry at {} with modifications\n{:#?}\nand binary modifications\n{:#?}",
                    &full_dn,
                    mods,
                    bin_mods
                );
                let mut combined_mods = bin_mods.to_owned();
                combined_mods.extend(mods_as_bin_mods(mods));
                let modify_failed = |source| LdapOperationError::OperationFailed {
                    operation: Box::new(FailedLdapOperation::Modify {
                        dn: full_dn.clone(),
                    }),
                    source,
                };
                ldap.with_controls(controls.to_owned())
                    .modify(&full_dn, combined_mods.to_vec())
                    .await
                    .map_err(modify_failed)?
                    .success()
                    .map_err(modify_failed)?;
            }
        }
    }

    Ok(())
}

/// helper function to search an LDAP server and generate [LDAPEntry] values
/// with the base DN removed to make them server-independent
///
/// # Errors
///
/// fails if the underlying ldap_search fails
#[instrument(skip(ldap, entries))]
pub async fn search_entries(
    ldap: &mut Ldap,
    base_dn: &str,
    search_base: &str,
    scope: ldap3::Scope,
    filter: &str,
    attrs: &[String],
    entries: &mut HashMap<String, LDAPEntry>,
) -> Result<(), LdapOperationError> {
    let it = ldap_search(
        ldap,
        &format!("{search_base},{base_dn}"),
        scope,
        filter,
        attrs.to_owned(),
    )
    .await?;
    for entry in it {
        tracing::debug!("Found entry {}", entry.dn);
        if let Some(s) = entry.dn.strip_suffix(&format!(",{base_dn}")) {
            entries.insert(
                s.to_string(),
                LDAPEntry {
                    dn: s.to_string(),
                    attrs: entry.attrs,
                    bin_attrs: entry.bin_attrs,
                },
            );
        } else {
            tracing::error!(
                "Failed to remove base dn {} from entry DN {}",
                base_dn,
                entry.dn
            );
        }
    }
    Ok(())
}

/// generate an [ldap3::Mod] if there is a DN-valued attribute in the source
/// entry that needs its base DN translated to the destination base DN
///
/// # Errors
///
/// Returns `LdapOperationError` if there is an issue parsing OIDs or if a required attribute is missing.
#[instrument(skip(
    source_entry,
    source_ldap_schema,
    source_base_dn,
    destination_entry,
    destination_base_dn,
    ignore_object_classes,
))]
pub fn mod_value(
    attr_name: &str,
    source_entry: &LDAPEntry,
    source_ldap_schema: &LDAPSchema,
    source_base_dn: &str,
    destination_entry: Option<&LDAPEntry>,
    destination_base_dn: &str,
    ignore_object_classes: &[String],
) -> Result<Option<ldap3::Mod<String>>, LdapOperationError> {
    if let Some(values) = source_entry.attrs.get(attr_name) {
        let mut replacement_values = HashSet::from_iter(values.iter().cloned());
        if attr_name == "objectClass" {
            for io in ignore_object_classes {
                replacement_values.remove(io);
            }
        }
        let attr_type_syntax =
            source_ldap_schema.find_attribute_type_property(attr_name, |at| at.syntax.as_ref());
        tracing::trace!(
            "Attribute type syntax for altered attribute {}: {:#?}",
            attr_name,
            attr_type_syntax
        );
        if let Some(syntax) = attr_type_syntax
            && (*DN_SYNTAX_OID)
                .as_ref()
                .map_err(|e| OIDError(*e))?
                .eq(syntax)
        {
            tracing::trace!(
                "Replacing base DN {} with base DN {}",
                source_base_dn,
                destination_base_dn
            );
            replacement_values = replacement_values
                .into_iter()
                .map(|s| s.replace(source_base_dn, destination_base_dn))
                .collect();
        }
        if let Some(destination_entry) = destination_entry
            && let Some(destination_values) = destination_entry.attrs.get(attr_name)
        {
            let mut replacement_values_sorted: Vec<String> =
                replacement_values.iter().cloned().collect();
            replacement_values_sorted.sort();
            let mut destination_values: Vec<String> = destination_values.to_vec();
            destination_values.sort();
            tracing::trace!(
                "Checking if replacement values and destination values are identical (case sensitive):\n{:#?}\n{:#?}",
                destination_values,
                replacement_values_sorted
            );
            if replacement_values_sorted == destination_values {
                tracing::trace!(
                    "Skipping attribute {} because replacement values and destination values are identical (case sensitive)",
                    attr_name
                );
                return Ok(None);
            }
            let attr_type_equality = source_ldap_schema
                .find_attribute_type_property(attr_name, |at| at.equality.as_ref());
            tracing::trace!(
                "Attribute type equality for altered attribute {}: {:#?}",
                attr_name,
                attr_type_equality
            );
            if let Some(equality) = &attr_type_equality
                && equality.describes_case_insensitive_match()
            {
                let mut lower_destination_values: Vec<String> = destination_values
                    .iter()
                    .map(|s| s.to_lowercase())
                    .collect();
                lower_destination_values.sort();
                let mut lower_replacement_values: Vec<String> = replacement_values
                    .iter()
                    .map(|s| s.to_lowercase())
                    .collect();
                lower_replacement_values.sort();
                tracing::trace!(
                    "Checking if replacement values and destination values are identical (case insensitive):\n{:#?}\n{:#?}",
                    lower_destination_values,
                    lower_replacement_values
                );
                if lower_destination_values == lower_replacement_values {
                    tracing::trace!(
                        "Skipping attribute {} because replacement values and destination values are identical (case insensitive)",
                        attr_name
                    );
                    return Ok(None);
                }
            }
        }
        Ok(Some(ldap3::Mod::Replace(
            attr_name.to_string(),
            replacement_values,
        )))
    } else {
        Ok(Some(ldap3::Mod::Delete(
            attr_name.to_string(),
            HashSet::new(),
        )))
    }
}

/// diff two sets of LDAPEntries which had their base DNs removed
/// and generates LDAP operations (add, update, delete) to apply to
/// the destination to make it identical to the source
///
/// # Errors
///
/// Returns `LdapOperationError` if there is an issue parsing OIDs or if a required attribute is missing.
#[expect(
    clippy::too_many_arguments,
    reason = "factoring parameters into objects is not sensible since this is basically standalone without many connections to the rest of the crate"
)]
#[instrument(skip(source_ldap_schema))]
pub fn diff_entries(
    source_entries: &HashMap<String, LDAPEntry>,
    destination_entries: &HashMap<String, LDAPEntry>,
    source_base_dn: &str,
    destination_base_dn: &str,
    ignore_object_classes: &[String],
    ignore_attributes: &[String],
    source_ldap_schema: &LDAPSchema,
    add: bool,
    update: bool,
    delete: bool,
) -> Result<Vec<LDAPOperation>, LdapOperationError> {
    let diff = Diff::diff(source_entries, destination_entries);
    tracing::trace!("Diff:\n{:#?}", diff);
    let mut ldap_operations: Vec<LDAPOperation> = vec![];
    for (altered_dn, change) in diff.altered {
        tracing::trace!("Processing altered DN {}", altered_dn);
        let source_entry: Option<&LDAPEntry> = source_entries.get(&altered_dn);
        let destination_entry: Option<&LDAPEntry> = destination_entries.get(&altered_dn);
        if let Some(source_entry) = source_entry {
            let mut ldap_mods: Vec<ldap3::Mod<String>> = vec![];
            let mut ldap_bin_mods: Vec<ldap3::Mod<Vec<u8>>> = vec![];
            for (attr_name, attr_value_changes) in &change.attrs.altered {
                if ignore_attributes.contains(attr_name) {
                    continue;
                }
                for attr_value_change in &attr_value_changes.0 {
                    match attr_value_change {
                        VecDiffType::Removed { .. }
                        | VecDiffType::Inserted { .. }
                        | VecDiffType::Altered { .. } => {
                            let m = mod_value(
                                attr_name,
                                source_entry,
                                source_ldap_schema,
                                source_base_dn,
                                destination_entry,
                                destination_base_dn,
                                ignore_object_classes,
                            )?;
                            if let Some(m) = m
                                && !ldap_mods.contains(&m)
                            {
                                ldap_mods.push(m);
                            }
                        }
                    }
                }
            }
            for attr_name in &change.attrs.removed {
                if ignore_attributes.contains(attr_name) {
                    continue;
                }
                let mut replacement_values = HashSet::from_iter(
                    source_entry
                        .attrs
                        .get(attr_name)
                        .ok_or(LdapOperationError::MissingAttribute(attr_name.clone()))?
                        .iter()
                        .cloned(),
                );
                if attr_name == "objectClass" {
                    for io in ignore_object_classes {
                        replacement_values.remove(io);
                    }
                }
                let attr_type_syntax = source_ldap_schema
                    .find_attribute_type_property(attr_name, |at| at.syntax.as_ref());
                tracing::trace!(
                    "Attribute type syntax for deleted attribute {}: {:#?}",
                    attr_name,
                    attr_type_syntax
                );
                if let Some(syntax) = attr_type_syntax
                    && (*DN_SYNTAX_OID)
                        .as_ref()
                        .map_err(|e| OIDError(*e))?
                        .eq(syntax)
                {
                    tracing::trace!(
                        "Replacing base DN {} with base DN {}",
                        source_base_dn,
                        destination_base_dn
                    );
                    replacement_values = replacement_values
                        .into_iter()
                        .map(|s| s.replace(source_base_dn, destination_base_dn))
                        .collect();
                }
                ldap_mods.push(ldap3::Mod::Add(attr_name.to_string(), replacement_values));
            }
            for (attr_name, attr_value_changes) in &change.bin_attrs.altered {
                if ignore_attributes.contains(attr_name) {
                    continue;
                }
                for attr_value_change in &attr_value_changes.0 {
                    match attr_value_change {
                        VecDiffType::Removed { .. }
                        | VecDiffType::Inserted { .. }
                        | VecDiffType::Altered { .. } => {
                            if let Some(values) = source_entry.bin_attrs.get(attr_name) {
                                let replace_mod = ldap3::Mod::Replace(
                                    attr_name.as_bytes().to_vec(),
                                    HashSet::from_iter(values.iter().cloned()),
                                );
                                if !ldap_bin_mods.contains(&replace_mod) {
                                    ldap_bin_mods.push(replace_mod);
                                }
                            } else {
                                ldap_bin_mods.push(ldap3::Mod::Delete(
                                    attr_name.as_bytes().to_vec(),
                                    HashSet::new(),
                                ));
                            }
                        }
                    }
                }
            }
            for attr_name in &change.bin_attrs.removed {
                if ignore_attributes.contains(attr_name) {
                    continue;
                }
                ldap_bin_mods.push(ldap3::Mod::Add(
                    attr_name.as_bytes().to_vec(),
                    HashSet::from_iter(
                        source_entry
                            .bin_attrs
                            .get(attr_name)
                            .ok_or(LdapOperationError::MissingAttribute(attr_name.clone()))?
                            .iter()
                            .cloned(),
                    ),
                ));
            }
            if update && !(ldap_mods.is_empty() && ldap_bin_mods.is_empty()) {
                ldap_operations.push(LDAPOperation::Modify {
                    dn: source_entry.dn.clone(),
                    mods: ldap_mods,
                    bin_mods: ldap_bin_mods,
                });
            }
        } else if delete {
            ldap_operations.push(LDAPOperation::Delete {
                dn: altered_dn.clone(),
            });
        }
    }
    for removed_dn in diff.removed {
        if add {
            let mut new_entry = source_entries[&removed_dn].clone();
            for ia in ignore_attributes {
                new_entry.attrs.remove(ia);
                new_entry.bin_attrs.remove(ia);
            }
            if let Some((k, v)) = new_entry.attrs.remove_entry("objectClass") {
                let ioc = &ignore_object_classes;
                let new_v = v.into_iter().filter(|x| !ioc.contains(x)).collect();
                new_entry.attrs.insert(k, new_v);
            }
            for (attr_name, attr_values) in &mut new_entry.attrs {
                let attr_type_syntax = source_ldap_schema
                    .find_attribute_type_property(attr_name, |at| at.syntax.as_ref());
                tracing::trace!(
                    "Attribute type syntax for attribute {} in deleted entry {}: {:#?}",
                    attr_name,
                    removed_dn,
                    attr_type_syntax
                );
                if let Some(syntax) = attr_type_syntax
                    && (*DN_SYNTAX_OID)
                        .as_ref()
                        .map_err(|e| OIDError(*e))?
                        .eq(syntax)
                {
                    tracing::trace!(
                        "Replacing base DN {} with base DN {}",
                        source_base_dn,
                        destination_base_dn
                    );
                    for s in attr_values.iter_mut() {
                        *s = s.replace(source_base_dn, destination_base_dn);
                    }
                }
            }
            ldap_operations.push(LDAPOperation::Add(new_entry));
        }
    }

    let mut ldap_operations = without_covered_deletes(ldap_operations);
    ldap_operations.sort_by(|a, b| {
        a.operation_apply_cmp(b)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    Ok(ldap_operations)
}

/// split a DN into its RDNs normalized for comparison (see [normalize_rdn])
fn normalized_rdns(dn: &str) -> Vec<String> {
    split_dn(dn).into_iter().map(normalize_rdn).collect()
}

/// remove delete operations for entries below another entry that is deleted
/// too
///
/// a delete is applied with [delete_recursive], which already removes the
/// whole subtree, so the deletes of the descendants would only fail because
/// their entries no longer exist
fn without_covered_deletes(ldap_operations: Vec<LDAPOperation>) -> Vec<LDAPOperation> {
    let deleted_dns: HashSet<Vec<String>> = ldap_operations
        .iter()
        .filter_map(|operation| match operation {
            LDAPOperation::Delete { dn } => Some(normalized_rdns(dn)),
            LDAPOperation::Add(_) | LDAPOperation::Modify { .. } => None,
        })
        .collect();
    ldap_operations
        .into_iter()
        .filter(|operation| match operation {
            LDAPOperation::Delete { dn } => {
                let rdns = normalized_rdns(dn);
                // every proper suffix of the RDN list is the DN of an ancestor
                let covered = (1..rdns.len())
                    .filter_map(|i| rdns.get(i..))
                    .any(|ancestor| deleted_dns.contains(ancestor));
                if covered {
                    tracing::trace!(
                        "Skipping delete of {} since an ancestor is deleted recursively",
                        dn
                    );
                }
                !covered
            }
            LDAPOperation::Add(_) | LDAPOperation::Modify { .. } => true,
        })
        .collect()
}

#[cfg(test)]
mod test {
    use super::*;
    use pretty_assertions::assert_eq;

    /// the base DN used in the tests
    const BASE: &str = "dc=prod,dc=rzbi,dc=saltation,dc=de";

    #[test]
    fn test_split_dn() {
        assert_eq!(
            split_dn("uid=foo, ou=people,dc=example"),
            vec!["uid=foo", "ou=people", "dc=example"],
            "whitespace around RDNs should be trimmed"
        );
        assert_eq!(
            split_dn(r"cn=Doe\, John,ou=people"),
            vec![r"cn=Doe\, John", "ou=people"],
            "escaped commas should not split RDNs"
        );
        assert_eq!(split_dn(""), Vec::<&str>::new(), "the empty DN has no RDNs");
    }

    #[test]
    fn test_without_covered_deletes() {
        let delete = |dn: &str| LDAPOperation::Delete { dn: dn.to_string() };
        let operations = vec![
            delete("ou=accounts,cn=gone.example,ou=devices"),
            delete("cn=gone.example,ou=devices"),
            delete(r"uid=root,ou=accounts,CN=Gone.Example, ou=devices"),
            delete(r"cn=gone.example\,other,ou=devices"),
            delete("cn=other.example,ou=devices"),
            LDAPOperation::Add(LDAPEntry {
                dn: "ou=accounts,cn=gone.example,ou=devices".to_string(),
                attrs: HashMap::new(),
                bin_attrs: HashMap::new(),
            }),
        ];
        assert_eq!(
            without_covered_deletes(operations)
                .iter()
                .map(|operation| match operation {
                    LDAPOperation::Delete { dn } => format!("delete {dn}"),
                    LDAPOperation::Add(entry) => format!("add {}", entry.dn),
                    LDAPOperation::Modify { dn, .. } => format!("modify {dn}"),
                })
                .collect::<Vec<_>>(),
            vec![
                "delete cn=gone.example,ou=devices",
                r"delete cn=gone.example\,other,ou=devices",
                "delete cn=other.example,ou=devices",
                "add ou=accounts,cn=gone.example,ou=devices",
            ],
            "deletes below a deleted entry should be dropped (case-insensitively, escaped commas respected), others kept"
        );
    }

    #[test]
    fn test_classify_entry_missing() {
        let requested = format!("ou=sshkeys,uid=foo,ou=people,{BASE}");
        let matched = format!("uid=foo,ou=people,{BASE}");
        assert_eq!(
            NoSuchObject::classify(&requested, &matched).kind,
            NoSuchObjectKind::EntryMissing,
            "matched DN is the parent of the requested DN"
        );
    }

    #[test]
    fn test_classify_ancestor_missing() {
        let requested = format!("ou=sshkeys,uid=foo,ou=people,{BASE}");
        let matched = format!("ou=people,{BASE}");
        assert_eq!(
            NoSuchObject::classify(&requested, &matched).kind,
            NoSuchObjectKind::AncestorMissing {
                first_missing: format!("uid=foo,ou=people,{BASE}"),
            },
            "the first missing DN is the one directly below the matched DN"
        );
    }

    #[test]
    fn test_classify_ancestor_missing_ignores_case_and_spaces() {
        let requested = format!("ou=sshkeys,uid=foo, ou=people,{BASE}");
        let matched = format!("OU = People,{BASE}");
        assert_eq!(
            NoSuchObject::classify(&requested, &matched).kind,
            NoSuchObjectKind::AncestorMissing {
                first_missing: format!("uid=foo,ou=people,{BASE}"),
            },
            "case and whitespace differences should not prevent the classification"
        );
    }

    #[test]
    fn test_classify_top_level_ou_missing() {
        let requested = format!("uid=foo,ou=peeple,{BASE}");
        assert_eq!(
            NoSuchObject::classify(&requested, BASE).kind,
            NoSuchObjectKind::AncestorMissing {
                first_missing: format!("ou=peeple,{BASE}"),
            },
            "a missing top-level OU below the base DN is a missing ancestor"
        );
    }

    #[test]
    fn test_classify_nothing_matched() {
        let requested = "uid=foo,ou=people,dc=wrong,dc=de";
        assert_eq!(
            NoSuchObject::classify(requested, "").kind,
            NoSuchObjectKind::NothingMatched,
            "an empty matched DN means not even the base DN exists"
        );
    }

    #[test]
    fn test_classify_unrelated_matched() {
        let requested = format!("uid=foo,ou=people,{BASE}");
        let matched = format!("ou=devices,{BASE}");
        assert_eq!(
            NoSuchObject::classify(&requested, &matched).kind,
            NoSuchObjectKind::Unclassified,
            "a matched DN that is not an ancestor can not be classified"
        );
        assert_eq!(
            NoSuchObject::classify(&requested, &requested).kind,
            NoSuchObjectKind::Unclassified,
            "a matched DN identical to the requested DN can not be classified"
        );
    }

    #[test]
    fn test_operation_failed_display() {
        let error = LdapOperationError::OperationFailed {
            operation: Box::new(FailedLdapOperation::Search {
                base: format!("ou=sshkeys,uid=foo,ou=people,{BASE}"),
                scope: Scope::OneLevel,
                filter: "(objectClass=sshPublicKey)".to_string(),
                attrs: vec!["sshPublicKeyFingerprint".to_string()],
            }),
            source: ldap3::LdapError::LdapResult {
                result: ldap3::LdapResult {
                    rc: 32,
                    matched: format!("ou=people,{BASE}"),
                    text: String::new(),
                    refs: vec![],
                    ctrls: vec![],
                },
            },
        };
        assert_eq!(
            error.to_string(),
            format!(
                "LDAP search (base: 'ou=sshkeys,uid=foo,ou=people,{BASE}', scope: one, filter: '(objectClass=sshPublicKey)', attributes: sshPublicKeyFingerprint) failed: 'uid=foo,ou=people,{BASE}' does not exist, so neither does 'ou=sshkeys,uid=foo,ou=people,{BASE}' (noSuchObject, deepest existing ancestor: 'ou=people,{BASE}')\n  to reproduce: ldapsearch -Q -LLL -o ldif-wrap=no -b 'ou=sshkeys,uid=foo,ou=people,{BASE}' -s one '(objectClass=sshPublicKey)' sshPublicKeyFingerprint"
            ),
            "the error message should contain the operation, the classification and the reproduction command"
        );
        assert!(
            error.no_such_object().is_some(),
            "the error should be classified as noSuchObject"
        );
    }
}
