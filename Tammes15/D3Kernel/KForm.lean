import Tammes15.D3Kernel.Bits

namespace Tammes15.D3Kernel.KForm

open Tammes15 Tammes15.D3lp Tammes15.D3Kernel

def laneK (x i : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.shiftLeft i 3)) 255

def iterK (face i j : ℕ) : ℕ := @Nat.rec (fun _ => ℕ) i (fun _ cur => laneK face cur) j

def periodGoK (face i fuel : ℕ) : ℕ → ℕ → ℕ :=
  @Nat.rec (fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0)
    (fun _ ih cur t => @Bool.rec (fun _ => ℕ) (ih (laneK face cur) (Nat.add t 1)) t (Nat.beq (laneK face cur) i))
    fuel

def periodK (face i : ℕ) : ℕ := periodGoK face i 6 i 1

def bitsK (x o w : ℕ) : ℕ := Nat.land (Nat.shiftRight x o) (Nat.sub (Nat.shiftLeft 1 w) 1)

def meanK (g v : ℕ) : ℕ := Nat.land (Nat.shiftRight g (Nat.add 4160 (Nat.shiftLeft v 4))) 65535

def DK (g : ℕ) : ℕ := Nat.land g 255

def nvCK (g : ℕ) : ℕ := Nat.land (Nat.shiftRight g 16) 255

def kK (g : ℕ) : ℕ := Nat.land (Nat.shiftRight g 8) 255

def baseK (g m : ℕ) : ℕ := Nat.land (Nat.shiftRight g (Nat.add 32 (Nat.shiftLeft m 3))) 255

theorem bitsK_eq (x o w : ℕ) : bitsK x o w = bits x o w := by
  unfold bitsK bits
  have hshift : Nat.shiftLeft 1 w = 2 ^ w := by
    calc
      Nat.shiftLeft 1 w = 1 * 2 ^ w := by simpa using Nat.shiftLeft_eq 1 w
      _ = 2 ^ w := by simp
  rw [hshift, Nat.land_eq]
  have hsub : Nat.sub (2 ^ w) 1 = 2 ^ w - 1 := rfl
  rw [hsub, Nat.and_two_pow_sub_one_eq_mod]
  simp [Nat.shiftRight_eq_div_pow]

theorem laneK_eq (x i : ℕ) : laneK x i = D3lp.lane x i := by
  unfold laneK D3lp.lane
  have hshift : Nat.shiftLeft i 3 = 8 * i := by
    calc
      Nat.shiftLeft i 3 = i * 2 ^ 3 := Nat.shiftLeft_eq i 3
      _ = i * 8 := by norm_num
      _ = 8 * i := Nat.mul_comm i 8
  rw [hshift]
  have h255 : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
  rw [h255]
  simpa using (Nat.and_two_pow_sub_one_eq_mod (x >>> (8 * i)) 8)

theorem laneK_face (g i : ℕ) (hi : i < 256) : laneK (Nat.shiftRight g 64) i = (Ctx.code g).faceAt i := by
  rw [laneK_eq]
  show ((g >>> 64) >>> (8 * i)) % 256 = ((g / 2 ^ 64 % 2 ^ 2048) >>> (8 * i)) % 256
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_div_two_pow]
  by_cases hj : j < 8
  · have h : 8 * i + j < 2048 := by omega
    simp only [hj, h, decide_true, Bool.true_and]
    rw [Nat.add_comm 64]
  · simp [hj]

theorem laneK_lt (x i : ℕ) : laneK x i < 256 := lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem iterK_eq (g i j : ℕ) (hi : i < 256) : iterK (Nat.shiftRight g 64) i j = (Ctx.code g).faceIter i j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlt : iterK (Nat.shiftRight g 64) i j < 256 := by
      cases j with
      | zero => exact hi
      | succ j => exact laneK_lt _ _
    show laneK (Nat.shiftRight g 64) (iterK (Nat.shiftRight g 64) i j) =
      (Ctx.code g).faceAt ((Ctx.code g).faceIter i j)
    rw [laneK_face g _ hlt, ih]

theorem periodGoK_eq (g i fuel cur t : ℕ) (hc : cur < 256) :
    periodGoK (Nat.shiftRight g 64) i fuel cur t = (Ctx.code g).periodGo i fuel cur t := by
  induction fuel generalizing cur t with
  | zero => rfl
  | succ n ih =>
    have hfaceRaw : laneK (Nat.shiftRight g 64) cur = (Ctx.code g).faceAt cur := by
      exact laneK_face g cur hc

    have hface : laneK (g >>> 64) cur = (Ctx.code g).faceAt cur := hfaceRaw
    simp [periodGoK, GCode.periodGo]

    by_cases hbeq : (laneK (g >>> 64) cur).beq i = true
    ·
      have h_eq_cur : laneK (g >>> 64) cur = i :=
        Nat.eq_of_beq_eq_true hbeq
      have h_eq_face : (Ctx.code g).faceAt cur = i := by
        rw [← hface, h_eq_cur]
      simp [hbeq, h_eq_face]
    ·
      have hbeqFalse : (laneK (g >>> 64) cur).beq i = false :=
        Bool.eq_false_of_not_eq_true hbeq
      have h_ne_face : (Ctx.code g).faceAt cur ≠ i := by
        intro h_eq
        apply hbeq
        rw [hface, h_eq]
        simp
      have hfaceCurLt : (Ctx.code g).faceAt cur < 256 := by
        rw [← hfaceRaw]
        unfold laneK
        have hle : Nat.land (Nat.shiftRight (Nat.shiftRight g 64) (Nat.shiftLeft cur 3)) 255 ≤ 255 :=
          Nat.and_le_right
        omega
      have ih' := ih ((Ctx.code g).faceAt cur) (t+1) hfaceCurLt
      simp [hbeqFalse]

      have hLHS : (Nat.rec (motive := fun x => ℕ → ℕ → ℕ) (fun x x_1 => 0)
        (fun x ih cur t => Bool.rec (ih (laneK (g >>> 64) cur) (t + 1)) t ((laneK (g >>> 64) cur).beq i)) n
        (laneK (g >>> 64) cur) (t + 1)) = periodGoK (Nat.shiftRight g 64) i n (laneK (Nat.shiftRight g 64) cur) (t+1) := by
        rfl
      rw [hLHS]
      rw [hfaceRaw]
      rw [ih']
      simp [h_ne_face]

theorem periodK_eq (g i : ℕ) (hi : i < 256) : periodK (Nat.shiftRight g 64) i = (Ctx.code g).period i :=
  periodGoK_eq g i 6 i 1 hi

theorem meanK_eq (g v : ℕ) : meanK g v = Ctx.mean g v := by
  unfold meanK Ctx.mean bits
  have h65535 : (65535 : ℕ) = 2 ^ 16 - 1 := by norm_num
  rw [h65535]
  have hshift : Nat.shiftLeft v 4 = 16 * v := by
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq_mul_pow]
    ring
  rw [hshift, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  have hadd : Nat.add 4160 (16 * v) = 4160 + 16 * v := by rfl
  rw [hadd]
  simpa using Nat.and_two_pow_sub_one_eq_mod (g / 2 ^ (4160 + 16 * v)) 16

theorem DK_eq (g : ℕ) : DK g = Ctx.D g := by
  unfold DK Ctx.D
  unfold bits
  simp
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (256 : ℕ) = 2^8 by norm_num]
  rw [Nat.testBit_land]
  rw [show (255 : ℕ) = 2^8 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
  rw [Nat.testBit_mod_two_pow]
  rw [Bool.and_comm]

theorem nvCK_eq (g : ℕ) : nvCK g = Ctx.nv g := land_shiftRight g 16 8

theorem kK_eq (g : ℕ) : kK g = Ctx.k g := land_shiftRight g 8 8

theorem baseK_eq (g m : ℕ) : baseK g m = Ctx.base g m := by
  have h : Nat.add 32 (Nat.shiftLeft m 3) = 32 + 8 * m := by
    show 32 + m <<< 3 = 32 + 8 * m
    rw [Nat.shiftLeft_eq]; ring
  unfold baseK Ctx.base
  rw [h]
  exact land_shiftRight g (32 + 8 * m) 8

end Tammes15.D3Kernel.KForm
