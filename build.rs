use std::collections::BTreeSet;
use std::fs::{self, File};
use std::io::BufWriter;
use std::io::{Read, Write};

const INCLUDES: &'static [&'static str] = &[
    "Cargo.toml",
];
const IGNORES: &'static [&'static str] = &[
    "src/meta.rs",
    "src/main.rs",
];

fn main() {
    let mut paths = BTreeSet::new();
    for &path in INCLUDES.iter() {
        paths.insert(path.to_owned());
    }
    for entry in fs::read_dir("src/").unwrap().map(Result::unwrap) {
        let path = entry.path().to_str().unwrap().to_owned();
        assert!(path.starts_with("src/"));
        if path.ends_with(".rs") { paths.insert(path); }
    }
    for &path in IGNORES.iter() {
        paths.remove(path);
    }

    let mut context = md5::Context::new();
    let mut buf = Vec::with_capacity(1024);
    for path in paths {
        buf.clear();
        File::open(&path).unwrap().read_to_end(&mut buf).unwrap();
        context.consume(path.as_bytes());
        context.consume(&buf);
    }
    let hash = u128::from_be_bytes(context.compute().0);

    let out_dir = std::env::var("OUT_DIR").unwrap();
    let mut f = BufWriter::new(File::create(format!("{out_dir}/meta.rs")).unwrap());
    writeln!(f, "pub const FINGERPRINT: u128 = 0x{hash:0>32x}u128;").unwrap();
}
