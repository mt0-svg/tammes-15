// Link the system MPFR (libmpfr.so.6 is installed without the development symlink or headers).
fn main() {
    println!("cargo:rustc-link-arg=/usr/lib/x86_64-linux-gnu/libmpfr.so.6");
    println!("cargo:rustc-link-arg=/usr/lib/x86_64-linux-gnu/libgmp.so.10");
    println!("cargo:rerun-if-changed=build.rs");
}
