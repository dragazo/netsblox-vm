//! Various templated source files.

use std::prelude::v1::*;
use std::time::Duration;
use std::fmt::Write;

#[cfg(feature = "serde")]
use serde::Serialize;

use crate::process::ErrorSummary;

/// A status update in the structure expected by the standard js extension.
#[cfg_attr(feature = "serde", derive(Serialize))]
pub struct Status {
    pub running: bool,
    pub output: String,
    pub errors: Vec<ErrorSummary>,
}

/// An empty project.
///
/// This can be used for default initializing a project runner with a no-op project.
pub const EMPTY_PROJECT: &'static str = include_str!("assets/empty-proj.xml");

/// An entry to display in the syscall dropdown when running in server mode.
///
/// A single syscall can be listed multiple times, e.g., under different submenu categorizations.
/// These are not checked against the syscalls actually supported by your runtime.
/// You are responsible for implementing syscalls and ensuring they are accurately shown in the menu if desired.
pub enum SyscallMenu {
    /// A syscall name.
    Entry { label: String, value: String },
    /// A labeled submenu of syscalls.
    Submenu { label: String, content: Vec<SyscallMenu> },
}
impl SyscallMenu {
    /// Creates an instance of [`SyscallMenu::Entry`] with the given string as both the label and value.
    pub fn simple_entry(value: String) -> Self {
        SyscallMenu::Entry { label: value.clone(), value }
    }
    fn format(items: &[Self]) -> String {
        fn format_impl(value: &SyscallMenu, res: &mut String) {
            match value {
                SyscallMenu::Entry { label, value } => write!(res, "{label:?}:{value:?},").unwrap(),
                SyscallMenu::Submenu { label, content } => {
                    write!(res, "{label:?}:{{").unwrap();
                    for value in content {
                        format_impl(value, res);
                    }
                    res.push_str("},");
                }
            }
        }
        let mut res = String::with_capacity(64);
        res.push('{');
        for item in items {
            format_impl(item, &mut res);
        }
        res.push('}');
        res
    }
}
#[test]
fn test_syscall_menu_format() {
    assert_eq!(SyscallMenu::format(&[]), "{}");
    assert_eq!(SyscallMenu::format(&[SyscallMenu::Entry { label: "foo".into(), value: "gtr".into() }]), r#"{"foo":"gtr",}"#);
    assert_eq!(SyscallMenu::format(&[SyscallMenu::Entry { label: "foo".into(), value: "gtr".into() }, SyscallMenu::Entry { label: "bar".into(), value: "baz".into() }]), r#"{"foo":"gtr","bar":"baz",}"#);
    assert_eq!(SyscallMenu::format(&[SyscallMenu::simple_entry("foo".into()), SyscallMenu::Submenu { label: "test".into(), content: vec![] }, SyscallMenu::Entry { label: "bam".into(), value: "s".into() }]), r#"{"foo":"foo","test":{},"bam":"s",}"#);
    assert_eq!(SyscallMenu::format(&[SyscallMenu::Submenu { label: "tes\'  \' \"t\"f".into(), content: vec![] }]), r#"{"tes'  ' \"t\"f":{},}"#);
    assert_eq!(SyscallMenu::format(&[SyscallMenu::Entry { label: "foo\"b\'ar".into(), value: "gtr\'\"test".into() }]), r#"{"foo\"b'ar":"gtr'\"test",}"#);

}

/// Arguments used to construct a templated extension.
pub struct ExtensionArgs<'a> {
    /// The NetsBlox VM server to connect to.
    pub server: &'a str,
    /// The syscall menu structure to generate for syscall blocks.
    pub syscalls: &'a [SyscallMenu],
    /// A list of XML element names to omit from the XML sent to the VM server.
    pub omitted_elements: &'a [&'a str],
    /// The duration between successive calls to pull status from the VM server.
    pub pull_interval: Duration,
}
impl ExtensionArgs<'_> {
    /// Renders the provided arguments into an extension.
    pub fn render(&self) -> String {
        format!(include_str!("assets/extension.js"),
            server = self.server,
            syscalls = SyscallMenu::format(self.syscalls),
            omitted_elements = self.omitted_elements,
            pull_interval_ms = self.pull_interval.as_millis(),
        )
    }
}
