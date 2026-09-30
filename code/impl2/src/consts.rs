//! Constants of the N = 15 range, computed from their definitions with outward rounding.
//!
//! dlo: 53.65785 deg (a decimal below psi* = 53.65785012993267 deg; psi* > 53.65785 is checked
//! in code/impl2/consts_check.gp). dhi: 56.6716 deg (a decimal above the Fejes Toth bound
//! 56.671503548 deg for N = 15, same check). The search range [dlo, dhi] in radians is an outward
//! enclosure of [53.65785, 56.6716] deg; alpha range = alpha of the range (alpha increasing).

use crate::faces::{eval, Fam};
use crate::iv::I;
use crate::model::Params;
use crate::mp;

pub const DLO_DEG: &str = "53.65785";
pub const DHI_DEG: &str = "56.6716";

pub fn params(dlo_deg: &str, dhi_deg: &str) -> Params {
    let dlo = mp::deg2rad(dlo_deg).lo;
    let dhi = mp::deg2rad(dhi_deg).hi;
    let z = I::pt(0.0);
    let alo = eval::<I>(Fam::Alpha, &[I::pt(dlo), z, z, z]).unwrap()[0].lo;
    let ahi = eval::<I>(Fam::Alpha, &[I::pt(dhi), z, z, z]).unwrap()[0].hi;
    Params { dlo, dhi, alo, ahi }
}
