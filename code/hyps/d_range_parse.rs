//! The D3 program's own parse of its d range: `read_drange` (code/impl1/rust/src/deep.rs) on
//! data/params15ft.txt, with `parse_dn`, `parse_up` of the program's iv.rs.
//! Prints each bound as an integer significand times 2^-53, to compare with d_range.gp (2a).
#[allow(dead_code)]
#[path = "../impl1/rust/src/iv.rs"]
mod iv;

fn main() {
    let s = std::fs::read_to_string("../../data/params15ft.txt").expect("params");
    for line in s.lines() {
        let t: Vec<&str> = line.split_whitespace().collect();
        if t.len() >= 2 && (t[0] == "dlo" || t[0] == "dhi") {
            let f = if t[0] == "dlo" { iv::parse_dn(t[1]) } else { iv::parse_up(t[1]) };
            // f in [1/2, 1): f = m * 2^-53 with m the 52-bit fraction plus the implicit bit.
            let m = (f.to_bits() & ((1u64 << 52) - 1)) | (1u64 << 52);
            let e = ((f.to_bits() >> 52) & 0x7ff) as i64 - 1075;
            println!("{} {} parsed = {} * 2^{}", t[0], t[1], m, e);
        }
    }
}
