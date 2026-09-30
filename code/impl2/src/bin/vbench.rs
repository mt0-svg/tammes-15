use std::time::Instant;
use tverify::elem;
use tverify::iv::I;
use tverify::mp;
fn main() {
    mp::selftest();
    let n = 2_000_000;
    let _ = elem::sincos_pt(0.1);
    let t = Instant::now();
    let mut s = 0.0;
    for i in 0..n {
        let x = 0.5 + (i as f64) * 1e-6;
        s += elem::sincos_pt(x).0.lo;
    }
    println!("elem sincos_pt: {:.1} ns {s}", t.elapsed().as_secs_f64() / n as f64 * 1e9);
    for (name, f) in [("acos", 0), ("asin", 1), ("atan", 2), ("sincos iv", 3)] {
        let t = Instant::now();
        let mut s = 0.0;
        for i in 0..n {
            let x = 0.3 + (i as f64) * 1e-7;
            let v = I::new(x, x + 1e-9);
            s += match f {
                0 => elem::acos(v).unwrap().lo,
                1 => elem::asin(v).unwrap().lo,
                2 => elem::atan(v).lo,
                _ => elem::sincos(v).0.lo,
            };
        }
        println!("elem {name} interval: {:.1} ns {s}", t.elapsed().as_secs_f64() / n as f64 * 1e9);
    }
}
