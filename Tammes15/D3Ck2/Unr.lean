import Tammes15.D3Ck2.Ops

namespace D3Ck2

open Lanes24

noncomputable def mulU6 (O A B : Nat) : Nat :=
  let P := Nat.land (Nat.shiftLeft A 5) (Nat.mul (Nat.land B (Nat.shiftLeft O 5)) 576460752303423487)
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 4) (Nat.mul (Nat.land B (Nat.shiftLeft O 4)) 1152921504606846975))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 3) (Nat.mul (Nat.land B (Nat.shiftLeft O 3)) 2305843009213693951))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 2) (Nat.mul (Nat.land B (Nat.shiftLeft O 2)) 4611686018427387903))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 1) (Nat.mul (Nat.land B (Nat.shiftLeft O 1)) 9223372036854775807))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 0) (Nat.mul (Nat.land B (Nat.shiftLeft O 0)) 18446744073709551615))
  P

noncomputable def mulU13 (O A B : Nat) : Nat :=
  let P := Nat.land (Nat.shiftLeft A 12) (Nat.mul (Nat.land B (Nat.shiftLeft O 12)) 4503599627370495)
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 11) (Nat.mul (Nat.land B (Nat.shiftLeft O 11)) 9007199254740991))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 10) (Nat.mul (Nat.land B (Nat.shiftLeft O 10)) 18014398509481983))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 9) (Nat.mul (Nat.land B (Nat.shiftLeft O 9)) 36028797018963967))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 8) (Nat.mul (Nat.land B (Nat.shiftLeft O 8)) 72057594037927935))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 7) (Nat.mul (Nat.land B (Nat.shiftLeft O 7)) 144115188075855871))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 6) (Nat.mul (Nat.land B (Nat.shiftLeft O 6)) 288230376151711743))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 5) (Nat.mul (Nat.land B (Nat.shiftLeft O 5)) 576460752303423487))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 4) (Nat.mul (Nat.land B (Nat.shiftLeft O 4)) 1152921504606846975))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 3) (Nat.mul (Nat.land B (Nat.shiftLeft O 3)) 2305843009213693951))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 2) (Nat.mul (Nat.land B (Nat.shiftLeft O 2)) 4611686018427387903))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 1) (Nat.mul (Nat.land B (Nat.shiftLeft O 1)) 9223372036854775807))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 0) (Nat.mul (Nat.land B (Nat.shiftLeft O 0)) 18446744073709551615))
  P

noncomputable def mulU20 (O A B : Nat) : Nat :=
  let P := Nat.land (Nat.shiftLeft A 19) (Nat.mul (Nat.land B (Nat.shiftLeft O 19)) 35184372088831)
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 18) (Nat.mul (Nat.land B (Nat.shiftLeft O 18)) 70368744177663))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 17) (Nat.mul (Nat.land B (Nat.shiftLeft O 17)) 140737488355327))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 16) (Nat.mul (Nat.land B (Nat.shiftLeft O 16)) 281474976710655))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 15) (Nat.mul (Nat.land B (Nat.shiftLeft O 15)) 562949953421311))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 14) (Nat.mul (Nat.land B (Nat.shiftLeft O 14)) 1125899906842623))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 13) (Nat.mul (Nat.land B (Nat.shiftLeft O 13)) 2251799813685247))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 12) (Nat.mul (Nat.land B (Nat.shiftLeft O 12)) 4503599627370495))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 11) (Nat.mul (Nat.land B (Nat.shiftLeft O 11)) 9007199254740991))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 10) (Nat.mul (Nat.land B (Nat.shiftLeft O 10)) 18014398509481983))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 9) (Nat.mul (Nat.land B (Nat.shiftLeft O 9)) 36028797018963967))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 8) (Nat.mul (Nat.land B (Nat.shiftLeft O 8)) 72057594037927935))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 7) (Nat.mul (Nat.land B (Nat.shiftLeft O 7)) 144115188075855871))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 6) (Nat.mul (Nat.land B (Nat.shiftLeft O 6)) 288230376151711743))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 5) (Nat.mul (Nat.land B (Nat.shiftLeft O 5)) 576460752303423487))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 4) (Nat.mul (Nat.land B (Nat.shiftLeft O 4)) 1152921504606846975))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 3) (Nat.mul (Nat.land B (Nat.shiftLeft O 3)) 2305843009213693951))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 2) (Nat.mul (Nat.land B (Nat.shiftLeft O 2)) 4611686018427387903))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 1) (Nat.mul (Nat.land B (Nat.shiftLeft O 1)) 9223372036854775807))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 0) (Nat.mul (Nat.land B (Nat.shiftLeft O 0)) 18446744073709551615))
  P

noncomputable def mulU26 (O A B : Nat) : Nat :=
  let P := Nat.land (Nat.shiftLeft A 25) (Nat.mul (Nat.land B (Nat.shiftLeft O 25)) 549755813887)
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 24) (Nat.mul (Nat.land B (Nat.shiftLeft O 24)) 1099511627775))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 23) (Nat.mul (Nat.land B (Nat.shiftLeft O 23)) 2199023255551))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 22) (Nat.mul (Nat.land B (Nat.shiftLeft O 22)) 4398046511103))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 21) (Nat.mul (Nat.land B (Nat.shiftLeft O 21)) 8796093022207))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 20) (Nat.mul (Nat.land B (Nat.shiftLeft O 20)) 17592186044415))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 19) (Nat.mul (Nat.land B (Nat.shiftLeft O 19)) 35184372088831))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 18) (Nat.mul (Nat.land B (Nat.shiftLeft O 18)) 70368744177663))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 17) (Nat.mul (Nat.land B (Nat.shiftLeft O 17)) 140737488355327))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 16) (Nat.mul (Nat.land B (Nat.shiftLeft O 16)) 281474976710655))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 15) (Nat.mul (Nat.land B (Nat.shiftLeft O 15)) 562949953421311))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 14) (Nat.mul (Nat.land B (Nat.shiftLeft O 14)) 1125899906842623))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 13) (Nat.mul (Nat.land B (Nat.shiftLeft O 13)) 2251799813685247))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 12) (Nat.mul (Nat.land B (Nat.shiftLeft O 12)) 4503599627370495))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 11) (Nat.mul (Nat.land B (Nat.shiftLeft O 11)) 9007199254740991))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 10) (Nat.mul (Nat.land B (Nat.shiftLeft O 10)) 18014398509481983))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 9) (Nat.mul (Nat.land B (Nat.shiftLeft O 9)) 36028797018963967))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 8) (Nat.mul (Nat.land B (Nat.shiftLeft O 8)) 72057594037927935))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 7) (Nat.mul (Nat.land B (Nat.shiftLeft O 7)) 144115188075855871))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 6) (Nat.mul (Nat.land B (Nat.shiftLeft O 6)) 288230376151711743))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 5) (Nat.mul (Nat.land B (Nat.shiftLeft O 5)) 576460752303423487))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 4) (Nat.mul (Nat.land B (Nat.shiftLeft O 4)) 1152921504606846975))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 3) (Nat.mul (Nat.land B (Nat.shiftLeft O 3)) 2305843009213693951))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 2) (Nat.mul (Nat.land B (Nat.shiftLeft O 2)) 4611686018427387903))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 1) (Nat.mul (Nat.land B (Nat.shiftLeft O 1)) 9223372036854775807))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 0) (Nat.mul (Nat.land B (Nat.shiftLeft O 0)) 18446744073709551615))
  P

noncomputable def mulU28 (O A B : Nat) : Nat :=
  let P := Nat.land (Nat.shiftLeft A 27) (Nat.mul (Nat.land B (Nat.shiftLeft O 27)) 137438953471)
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 26) (Nat.mul (Nat.land B (Nat.shiftLeft O 26)) 274877906943))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 25) (Nat.mul (Nat.land B (Nat.shiftLeft O 25)) 549755813887))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 24) (Nat.mul (Nat.land B (Nat.shiftLeft O 24)) 1099511627775))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 23) (Nat.mul (Nat.land B (Nat.shiftLeft O 23)) 2199023255551))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 22) (Nat.mul (Nat.land B (Nat.shiftLeft O 22)) 4398046511103))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 21) (Nat.mul (Nat.land B (Nat.shiftLeft O 21)) 8796093022207))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 20) (Nat.mul (Nat.land B (Nat.shiftLeft O 20)) 17592186044415))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 19) (Nat.mul (Nat.land B (Nat.shiftLeft O 19)) 35184372088831))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 18) (Nat.mul (Nat.land B (Nat.shiftLeft O 18)) 70368744177663))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 17) (Nat.mul (Nat.land B (Nat.shiftLeft O 17)) 140737488355327))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 16) (Nat.mul (Nat.land B (Nat.shiftLeft O 16)) 281474976710655))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 15) (Nat.mul (Nat.land B (Nat.shiftLeft O 15)) 562949953421311))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 14) (Nat.mul (Nat.land B (Nat.shiftLeft O 14)) 1125899906842623))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 13) (Nat.mul (Nat.land B (Nat.shiftLeft O 13)) 2251799813685247))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 12) (Nat.mul (Nat.land B (Nat.shiftLeft O 12)) 4503599627370495))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 11) (Nat.mul (Nat.land B (Nat.shiftLeft O 11)) 9007199254740991))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 10) (Nat.mul (Nat.land B (Nat.shiftLeft O 10)) 18014398509481983))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 9) (Nat.mul (Nat.land B (Nat.shiftLeft O 9)) 36028797018963967))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 8) (Nat.mul (Nat.land B (Nat.shiftLeft O 8)) 72057594037927935))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 7) (Nat.mul (Nat.land B (Nat.shiftLeft O 7)) 144115188075855871))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 6) (Nat.mul (Nat.land B (Nat.shiftLeft O 6)) 288230376151711743))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 5) (Nat.mul (Nat.land B (Nat.shiftLeft O 5)) 576460752303423487))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 4) (Nat.mul (Nat.land B (Nat.shiftLeft O 4)) 1152921504606846975))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 3) (Nat.mul (Nat.land B (Nat.shiftLeft O 3)) 2305843009213693951))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 2) (Nat.mul (Nat.land B (Nat.shiftLeft O 2)) 4611686018427387903))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 1) (Nat.mul (Nat.land B (Nat.shiftLeft O 1)) 9223372036854775807))
  let P := Nat.add P (Nat.land (Nat.shiftLeft A 0) (Nat.mul (Nat.land B (Nat.shiftLeft O 0)) 18446744073709551615))
  P

noncomputable def sc28u (O X : Nat) : Nat × Nat :=
  let r := red28 O X
  let z := r.1
  let z2 := rsh O (mulU28 O z z) 28
  let z4 := rsh O (mulU26 O z2 (rsh O z2 2)) 26
  let z6 := rsh O (mulU20 O z4 (rsh O z2 8)) 20
  let z8 := rsh O (mulU13 O z4 (rsh O z4 14)) 14
  let z10 := rsh O (mulU6 O z8 (rsh O z2 22)) 6
  let c36 := Nat.sub (Nat.add (Nat.add (rep O 68719476736) (kc O z4 2863311531)) (kc O z8 1704352))
    (Nat.add (Nat.add (Nat.shiftLeft z2 7) (kc O z6 95443718)) (kc O z10 18937))
  let c := rsh O c36 8
  let q36 := Nat.sub (Nat.add (Nat.add (rep O 68719476736) (kc O z4 572662306)) (kc O z8 189372))
    (Nat.add (kc O z2 11453246123) (kc O z6 13634817))
  let q30 := rsh O q36 6
  let s := rsh O (mulU28 O q30 z) 30
  out28 O r.2.1 r.2.2 s c

end D3Ck2
