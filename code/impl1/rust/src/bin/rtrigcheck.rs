//! Checks the rigorous elementary functions of rtrig.rs against MPFR: for every sample point x,
//! the rtrig enclosure [lo, hi] must contain the correctly rounded bounds [RD f(x), RU f(x)]
//! returned by MPFR (hence the true value). Also checks the hard-coded constants (pi, atan(j/8)).
//! Reports failures and the largest enclosure width in ulps per function.
//! Usage: rtrigcheck [N] [SEED]   (N random points per function and range, default 1e6)

use tammes15::ivt::Iv;
use tammes15::mpfr;
use tammes15::rtrig;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        // splitmix64
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn unif(&mut self, a: f64, b: f64) -> f64 {
        a + (b - a) * ((self.next() >> 11) as f64 / (1u64 << 53) as f64)
    }
}

fn ulp(x: f64) -> f64 {
    let a = x.abs();
    if a == 0.0 {
        f64::from_bits(1)
    } else {
        a.next_up() - a
    }
}

struct Stat {
    name: &'static str,
    n: u64,
    fail: u64,
    maxw: f64,
    argw: f64,
}

fn check(st: &mut Stat, f: usize, x: f64, e: Iv) {
    let (lo, hi) = mpfr::enc(f, x);
    st.n += 1;
    if lo.is_nan() || hi.is_nan() {
        return;
    }
    if !(e.lo <= lo && hi <= e.hi) {
        st.fail += 1;
        if st.fail <= 10 {
            eprintln!("FAIL {} x = {x:e} ({:016x}): rtrig [{:e}, {:e}] mpfr [{:e}, {:e}]", st.name, x.to_bits(), e.lo, e.hi, lo, hi);
        }
    }
    let w = (e.hi - e.lo) / ulp(0.5 * (lo + hi));
    if w.is_finite() && w > st.maxw {
        st.maxw = w;
        st.argw = x;
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let n: u64 = a.get(1).map_or(1_000_000, |s| s.parse().unwrap());
    let seed: u64 = a.get(2).map_or(1, |s| s.parse().unwrap());
    let mut rng = Rng(seed);
    // constants
    let (plo, phi) = mpfr::pi_enc();
    assert!(rtrig::PI_T_LO == plo && rtrig::PI_T_HI == phi, "pi constant: mpfr [{plo:e}, {phi:e}]");
    for j in 1..=8 {
        let (lo, hi) = mpfr::enc(3, j as f64 / 8.0);
        let e = rtrig::atan_enc(j as f64 / 8.0);
        assert!(e.lo <= lo && hi <= e.hi, "atan({j}/8)");
    }
    println!("constants: pi and atan(j/8) enclosures agree with MPFR");
    let names = ["cos", "acos", "asin", "atan", "tan", "sin"];
    let mut stats: Vec<Stat> = names.iter().map(|&s| Stat { name: s, n: 0, fail: 0, maxw: 0.0, argw: 0.0 }).collect();
    let pi = std::f64::consts::PI;
    let special = [0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 1e-300, -1e-300, 5e-324, 1e-8, 0.0625, 0.125, 0.9375, 1.0 - 1e-16, -1.0 + 1e-16];
    for &x in special.iter() {
        check(&mut stats[0], 0, x, rtrig::cos_enc(x));
        check(&mut stats[5], 5, x, rtrig::sin_enc(x));
        check(&mut stats[3], 3, x, rtrig::atan_enc(x));
        check(&mut stats[4], 4, x, rtrig::tan_enc(x));
        if x.abs() <= 1.0 {
            check(&mut stats[1], 1, x, rtrig::acos_enc(x));
            check(&mut stats[2], 2, x, rtrig::asin_enc(x));
        }
    }
    for _ in 0..n {
        // cos, sin: uniform on [-10, 10], near multiples of pi/2, tiny
        let k = (rng.next() % 13) as f64 - 6.0;
        for x in [rng.unif(-10.0, 10.0), k * 0.5 * pi + rng.unif(-1e-6, 1e-6), k * 0.5 * pi + rng.unif(-0.8, 0.8), rng.unif(-1e-5, 1e-5)] {
            check(&mut stats[0], 0, x, rtrig::cos_enc(x));
            check(&mut stats[5], 5, x, rtrig::sin_enc(x));
        }
        // tan on (-pi/2, pi/2)
        for x in [rng.unif(-1.5707963267948966, 1.5707963267948966), 1.5707963267948966 - rng.unif(0.0, 1e-3)] {
            check(&mut stats[4], 4, x, rtrig::tan_enc(x));
        }
        // atan: uniform, log-uniform magnitudes, eighths boundaries
        let j = (rng.next() % 17) as f64 / 16.0;
        let lm = 10f64.powf(rng.unif(-20.0, 20.0));
        for x in [rng.unif(-2.0, 2.0), lm, -lm, j + rng.unif(-1e-9, 1e-9)] {
            check(&mut stats[3], 3, x, rtrig::atan_enc(x));
        }
        // acos, asin: uniform, near +-1, near 0
        let t = 10f64.powf(rng.unif(-16.0, 0.0));
        for x in [rng.unif(-1.0, 1.0), 1.0 - t, -1.0 + t, rng.unif(-1e-6, 1e-6)] {
            if x.abs() <= 1.0 {
                check(&mut stats[1], 1, x, rtrig::acos_enc(x));
                check(&mut stats[2], 2, x, rtrig::asin_enc(x));
            }
        }
    }
    let mut bad = 0;
    for s in &stats {
        println!("{:5} points {:9} failures {} max width {:.1} ulp (at x = {:e})", s.name, s.n, s.fail, s.maxw, s.argw);
        bad += s.fail;
    }
    if bad > 0 {
        println!("RTRIGCHECK FAILED");
        std::process::exit(1);
    }
    println!("RTRIGCHECK OK");
}
