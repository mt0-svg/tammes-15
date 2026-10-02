//! Log of the arithmetic of the program, for the differential test of Prims.lean (Section
//! 10.4 of the paper). Each call of an interval operation of ivt.rs (`add`, `sub`, `mul`,
//! `div`, `cos`, `sin`, `acos`, `asin`, `atan`, `tan`) and of a directed operation of iv.rs (`add_dn`
//! to `div_up`, and `(a + b).next_up()` in deep.rs `corner_ends`) records its arguments and its
//! result while the log is on. The values computed are unchanged: the wrappers return the value of
//! the original body. Only the outermost call is recorded: the operations an operation performs inside
//! itself are not, since the Lean model reads the operations as opaque fields.

use crate::ivt::Iv;
use std::cell::{Cell, RefCell};

/// Operation codes, in the order of the fields of `Rnd` (Arith.lean).
pub const OP_NAMES: [&str; 18] = [
    "add", "sub", "mul", "div", "cos", "sin", "acos", "asin", "atan", "tan", "addDn", "addUp", "subDn",
    "subUp", "mulDn", "mulUp", "divDn", "divUp",
];

#[derive(Clone, Copy, Debug)]
pub struct Entry {
    pub op: u8,
    pub a: [f64; 4],
    pub r: [f64; 2],
}

thread_local! {
    static ON: Cell<bool> = const { Cell::new(false) };
    static LOG: RefCell<Vec<Entry>> = const { RefCell::new(Vec::new()) };
    static DEPTH: Cell<u32> = const { Cell::new(0) };
}

pub fn start() {
    LOG.with(|l| l.borrow_mut().clear());
    ON.with(|o| o.set(true));
}

pub fn stop() -> Vec<Entry> {
    ON.with(|o| o.set(false));
    LOG.with(|l| std::mem::take(&mut *l.borrow_mut()))
}

/// Runs `f` one level deeper, and records `e(f())` when the call is outermost and the log is on.
#[inline]
fn run<T: Copy>(f: impl FnOnce() -> T, e: impl FnOnce(T) -> Entry) -> T {
    let d = DEPTH.with(|c| c.replace(c.get() + 1));
    let r = f();
    DEPTH.with(|c| c.set(d));
    if d == 0 && ON.with(|o| o.get()) {
        LOG.with(|l| l.borrow_mut().push(e(r)));
    }
    r
}

/// A binary interval operation.
#[inline]
pub fn iv2(op: u8, x: Iv, y: Iv, f: impl FnOnce() -> Iv) -> Iv {
    run(f, |r| Entry {
        op,
        a: [x.lo, x.hi, y.lo, y.hi],
        r: [r.lo, r.hi],
    })
}

/// A unary interval operation.
#[inline]
pub fn iv1(op: u8, x: Iv, f: impl FnOnce() -> Iv) -> Iv {
    run(f, |r| Entry {
        op,
        a: [x.lo, x.hi, 0.0, 0.0],
        r: [r.lo, r.hi],
    })
}

/// A directed point operation.
#[inline]
pub fn pt2(op: u8, a: f64, b: f64, f: impl FnOnce() -> f64) -> f64 {
    run(f, |r| Entry {
        op,
        a: [a, b, 0.0, 0.0],
        r: [r, 0.0],
    })
}

/// The operation `op` at the arguments `a`, with the log off (for the flip check).
pub fn eval(op: u8, a: [f64; 4]) -> [f64; 2] {
    let was = ON.with(|o| o.replace(false));
    let x = Iv::new(a[0], a[1]);
    let y = Iv::new(a[2], a[3]);
    let iv = |r: Iv| [r.lo, r.hi];
    let r = match op {
        0 => iv(x.add(y)),
        1 => iv(x.sub(y)),
        2 => iv(x.mul(y)),
        3 => iv(x.div(y)),
        4 => iv(x.cos()),
        5 => iv(x.sin()),
        6 => iv(x.acos()),
        7 => iv(x.asin()),
        8 => iv(x.atan()),
        9 => iv(x.tan()),
        10 => [crate::iv::add_dn(a[0], a[1]), 0.0],
        11 => [crate::iv::add_up(a[0], a[1]), 0.0],
        12 => [crate::iv::sub_dn(a[0], a[1]), 0.0],
        13 => [crate::iv::sub_up(a[0], a[1]), 0.0],
        14 => [crate::iv::mul_dn(a[0], a[1]), 0.0],
        15 => [crate::iv::mul_up(a[0], a[1]), 0.0],
        16 => [crate::iv::div_dn(a[0], a[1]), 0.0],
        _ => [crate::iv::div_up(a[0], a[1]), 0.0],
    };
    ON.with(|o| o.set(was));
    r
}

/// The number of arguments of `op` (floats).
pub fn arity(op: u8) -> usize {
    match op {
        0..=3 => 4,
        4..=9 => 2,
        _ => 2,
    }
}
