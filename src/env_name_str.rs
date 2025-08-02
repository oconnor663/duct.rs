use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};

/// An [`OsString`] that's case-insensitive on Windows, used for environment variable names.
#[derive(Clone)]
pub(crate) struct EnvNameString(OsString);

impl Debug for EnvNameString {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl From<OsString> for EnvNameString {
    fn from(name: OsString) -> Self {
        EnvNameString(name)
    }
}

impl AsRef<OsStr> for EnvNameString {
    fn as_ref(&self) -> &OsStr {
        &self.0
    }
}

impl PartialEq<Self> for EnvNameString {
    fn eq(&self, other: &Self) -> bool {
        // On Windows, env var names are case-insensitive
        #[cfg(windows)]
        match (self.0.to_str(), other.0.to_str()) {
            (Some(s1), Some(s2)) => s1.eq_ignore_ascii_case(s2),
            // If either name isn't valid Unicode then just leave it as is.
            _ => self.0 == other.0,
        }

        // On all other platforms, env var names are case-sensitive.
        #[cfg(not(windows))]
        {
            self.0 == other.0
        }
    }
}

impl Eq for EnvNameString {}

impl Hash for EnvNameString {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // On Windows, env var names are case-insensitive
        #[cfg(windows)]
        match self.0.to_str() {
            Some(s) => {
                // Uppercase each byte separately to avoid reallocating. This is similar to what
                // eq_ignore_ascii_case does internally.
                for &b in s.as_bytes() {
                    b.to_ascii_uppercase().hash(state);
                }
            }
            // If the name isn't valid Unicode then just leave it as is.
            None => self.0.hash(state),
        }

        // On all other platforms, env var names are case-sensitive.
        #[cfg(not(windows))]
        {
            self.0.hash(state);
        }
    }
}
