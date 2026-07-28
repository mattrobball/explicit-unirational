/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.FunctionField.TangentResidual
import all ExplicitUnirational.FunctionField.TangentResidual
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Y-split product reductions (Route B)

`gAff` has `Y`-degree 3 with leading coefficient `z = X 2`. Already-reduced forms have
`Y`-degree ≤ 2. Write `red = a₀ + a₁·Y + a₂·Y²` with `aᵢ` free of `Y`. Then only the
`Y³` and `Y⁴` summands of a square/product need reduction, via the base identities

```
  z · Y³ = y3c + gAff
  z · Y⁴ = y4c + (Y − 1) · gAff
```

Coefficient products are `Y`-free, so each `ring` goal is far smaller than a monolithic
bivariate product (cf. `redH2_sq_mod` raw 296 ≈ 8 min).

## Status (this module)

**Proved** (module build ≈ 5 min; axioms `propext` / `Classical.choice` / `Quot.sound`):

* base lemmas `z_mul_Y3_eq`, `z_mul_Y4_eq`, `high_Y34_reduce`
* `redH3_sq_mod` / `gAff_dvd_redH3_sq_sub`  (was the 755-monom product)
* `redTheta_sq_mod` / `gAff_dvd_redTheta_sq_sub`  (was the 546-monom product)

**Not yet in this module:** `redJ²`, `redTheta³`, `A·Θ·redH2sq`, and the final
Weierstrass remainder cancellation / congruence. Monolithic single-`ring` on those
products did not finish in multi-hour runs; the Y-split pattern above is the intended
route for the rest.
-/

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000

noncomputable section

open MvPolynomial

namespace ExplicitUnirational

/-! ## Base `Y³` / `Y⁴` reduction -/

/-- Remainder of `z·Y³` mod `gAff` (`Y`-degree ≤ 2). -/
public noncomputable def y3c : MvPolynomial (Fin 3) ℚ :=
  (X 0) ^ 3
    - (X 0) * (X 2)
    - (X 1) ^ 2 * (X 2)
    - (X 1)
    + (X 2)
/-- Remainder of `z·Y⁴` mod `gAff` (`Y`-degree ≤ 2). -/
public noncomputable def y4c : MvPolynomial (Fin 3) ℚ :=
  (X 0) ^ 3 * (X 1)
    - (X 0) ^ 3
    - (X 0) * (X 1) * (X 2)
    + (X 0) * (X 2)
    + (X 1) ^ 2 * (X 2)
    - (X 1) ^ 2
    + (X 1) * (X 2)
    + (X 1)
    - (X 2)

/-- **Base lemma.** `z · Y³ ≡ y3c (mod gAff)` as an exact polynomial identity. -/
public theorem z_mul_Y3_eq :
    (X 2) * (X 1) ^ 3 = y3c + gAff := by
  unfold y3c gAff
  ring

/-- **Base lemma.** `z · Y⁴ ≡ y4c (mod gAff)`. -/
public theorem z_mul_Y4_eq :
    (X 2) * (X 1) ^ 4 = y4c + ((X 1) - 1) * gAff := by
  unfold y4c gAff
  ring

/-- High-part reduction for `Y³`/`Y⁴` coefficients already factored through `z`. -/
public theorem high_Y34_reduce (c3p c4p : MvPolynomial (Fin 3) ℚ) :
    (X 2) * c3p * (X 1) ^ 3 + (X 2) * c4p * (X 1) ^ 4 =
      (c3p + c4p * ((X 1) - 1)) * gAff + (c3p * y3c + c4p * y4c) := by
  have h3 := z_mul_Y3_eq
  have h4 := z_mul_Y4_eq
  calc
    (X 2) * c3p * (X 1) ^ 3 + (X 2) * c4p * (X 1) ^ 4
        = c3p * ((X 2) * (X 1) ^ 3) + c4p * ((X 2) * (X 1) ^ 4) := by ring
    _ = c3p * (y3c + gAff) + c4p * (y4c + ((X 1) - 1) * gAff) := by rw [h3, h4]
    _ = (c3p + c4p * ((X 1) - 1)) * gAff + (c3p * y3c + c4p * y4c) := by ring

public theorem Ydeg2_sq_expand (a0 a1 a2 : MvPolynomial (Fin 3) ℚ) :
    (a0 + a1 * (X 1) + a2 * (X 1) ^ 2) ^ 2 =
      a0 ^ 2 + (2 * a0 * a1) * (X 1) + (a1 ^ 2 + 2 * a0 * a2) * (X 1) ^ 2
        + (2 * a1 * a2) * (X 1) ^ 3 + (a2 ^ 2) * (X 1) ^ 4 := by
  ring

public theorem Ydeg2_mul_expand (a0 a1 a2 b0 b1 b2 : MvPolynomial (Fin 3) ℚ) :
    (a0 + a1 * (X 1) + a2 * (X 1) ^ 2) * (b0 + b1 * (X 1) + b2 * (X 1) ^ 2) =
      (a0 * b0) + (a0 * b1 + a1 * b0) * (X 1)
        + (a0 * b2 + a1 * b1 + a2 * b0) * (X 1) ^ 2
        + (a1 * b2 + a2 * b1) * (X 1) ^ 3 + (a2 * b2) * (X 1) ^ 4 := by
  ring

/-! ## `redH3²` by Y-split -/

/-- Y⁰-coeff of `redH3`. -/
public noncomputable def redH3_a0 : MvPolynomial (Fin 3) ℚ :=
  - 729 * (X 0) ^ 9 * (X 2) ^ 5
    + 27 * (X 0) ^ 9 * (X 2) ^ 4
    - 243 * (X 0) ^ 9 * (X 2) ^ 3
    + 729 * (X 0) ^ 9 * (X 2) ^ 2
    - 729 * (X 0) ^ 9 * (X 2)
    + 6318 * (X 0) ^ 8 * (X 2) ^ 5
    + 1458 * (X 0) ^ 8 * (X 2) ^ 4
    - 18441 * (X 0) ^ 7 * (X 2) ^ 5
    - 6723 * (X 0) ^ 7 * (X 2) ^ 4
    - 6075 * (X 0) ^ 7 * (X 2) ^ 3
    + 5103 * (X 0) ^ 7 * (X 2) ^ 2
    - 2862 * (X 0) ^ 6 * (X 2) ^ 6
    + 17523 * (X 0) ^ 6 * (X 2) ^ 5
    + 8397 * (X 0) ^ 6 * (X 2) ^ 4
    + 13365 * (X 0) ^ 6 * (X 2) ^ 3
    - 8073 * (X 0) ^ 6 * (X 2) ^ 2
    - 3402 * (X 0) ^ 6 * (X 2)
    + 486 * (X 0) ^ 5 * (X 2) ^ 7
    + 18846 * (X 0) ^ 5 * (X 2) ^ 6
    + 6021 * (X 0) ^ 5 * (X 2) ^ 5
    + 3888 * (X 0) ^ 5 * (X 2) ^ 4
    - 3159 * (X 0) ^ 5 * (X 2) ^ 3
    - 4266 * (X 0) ^ 4 * (X 2) ^ 7
    - 37935 * (X 0) ^ 4 * (X 2) ^ 6
    - 15606 * (X 0) ^ 4 * (X 2) ^ 5
    - 18468 * (X 0) ^ 4 * (X 2) ^ 4
    + 11718 * (X 0) ^ 4 * (X 2) ^ 3
    + 3321 * (X 0) ^ 4 * (X 2) ^ 2
    + 216 * (X 0) ^ 3 * (X 2) ^ 8
    + 10503 * (X 0) ^ 3 * (X 2) ^ 7
    + 22086 * (X 0) ^ 3 * (X 2) ^ 6
    + 10233 * (X 0) ^ 3 * (X 2) ^ 5
    + 12150 * (X 0) ^ 3 * (X 2) ^ 4
    - 7344 * (X 0) ^ 3 * (X 2) ^ 3
    - 3159 * (X 0) ^ 3 * (X 2) ^ 2
    + 27 * (X 0) ^ 3
    - 954 * (X 0) ^ 2 * (X 2) ^ 8
    - 6534 * (X 0) ^ 2 * (X 2) ^ 7
    - 2403 * (X 0) ^ 2 * (X 2) ^ 6
    - 1701 * (X 0) ^ 2 * (X 2) ^ 5
    + 1215 * (X 0) ^ 2 * (X 2) ^ 4
    - 27 * (X 0) ^ 2 * (X 2) ^ 3
    + 27 * (X 0) * (X 2) ^ 9
    + 729 * (X 0) * (X 2) ^ 8
    + 162 * (X 0) * (X 2) ^ 7
    + 9 * (X 0) * (X 2) ^ 6
    - 28 * (X 2) ^ 9
/-- Y¹-coeff of `redH3`. -/
public noncomputable def redH3_a1 : MvPolynomial (Fin 3) ℚ :=
  729 * (X 0) ^ 8 * (X 2) ^ 5
    - 2187 * (X 0) ^ 8 * (X 2) ^ 4
    - 4212 * (X 0) ^ 7 * (X 2) ^ 5
    + 11664 * (X 0) ^ 7 * (X 2) ^ 4
    + 2916 * (X 0) ^ 7 * (X 2) ^ 3
    - 486 * (X 0) ^ 6 * (X 2) ^ 6
    + 7560 * (X 0) ^ 6 * (X 2) ^ 5
    - 15687 * (X 0) ^ 6 * (X 2) ^ 4
    - 6885 * (X 0) ^ 6 * (X 2) ^ 3
    - 3645 * (X 0) ^ 6 * (X 2) ^ 2
    + 2187 * (X 0) ^ 6 * (X 2)
    + 5724 * (X 0) ^ 5 * (X 2) ^ 6
    - 16200 * (X 0) ^ 5 * (X 2) ^ 5
    - 2916 * (X 0) ^ 5 * (X 2) ^ 4
    - 648 * (X 0) ^ 4 * (X 2) ^ 7
    - 14931 * (X 0) ^ 4 * (X 2) ^ 6
    + 45252 * (X 0) ^ 4 * (X 2) ^ 5
    + 14094 * (X 0) ^ 4 * (X 2) ^ 4
    + 8100 * (X 0) ^ 4 * (X 2) ^ 3
    - 6075 * (X 0) ^ 4 * (X 2) ^ 2
    + 3348 * (X 0) ^ 3 * (X 2) ^ 7
    + 3159 * (X 0) ^ 3 * (X 2) ^ 6
    - 34533 * (X 0) ^ 3 * (X 2) ^ 5
    - 11394 * (X 0) ^ 3 * (X 2) ^ 4
    - 15066 * (X 0) ^ 3 * (X 2) ^ 3
    + 9531 * (X 0) ^ 3 * (X 2) ^ 2
    + 3483 * (X 0) ^ 3 * (X 2)
    - 162 * (X 0) ^ 2 * (X 2) ^ 8
    - 3105 * (X 0) ^ 2 * (X 2) ^ 7
    + 9855 * (X 0) ^ 2 * (X 2) ^ 6
    + 2403 * (X 0) ^ 2 * (X 2) ^ 5
    + 1485 * (X 0) ^ 2 * (X 2) ^ 4
    - 1296 * (X 0) ^ 2 * (X 2) ^ 3
    + 324 * (X 0) * (X 2) ^ 8
    - 936 * (X 0) * (X 2) ^ 7
    - 108 * (X 0) * (X 2) ^ 6
    - 9 * (X 2) ^ 9
    + 27 * (X 2) ^ 8
/-- Y²-coeff of `redH3`. -/
public noncomputable def redH3_a2 : MvPolynomial (Fin 3) ℚ :=
  - 243 * (X 0) ^ 7 * (X 2) ^ 5
    + 1458 * (X 0) ^ 7 * (X 2) ^ 4
    - 2187 * (X 0) ^ 7 * (X 2) ^ 3
    + 675 * (X 0) ^ 6 * (X 2) ^ 5
    - 3807 * (X 0) ^ 6 * (X 2) ^ 4
    + 4617 * (X 0) ^ 6 * (X 2) ^ 3
    + 2187 * (X 0) ^ 6 * (X 2) ^ 2
    + 486 * (X 0) ^ 5 * (X 2) ^ 6
    - 2916 * (X 0) ^ 5 * (X 2) ^ 5
    + 4374 * (X 0) ^ 5 * (X 2) ^ 4
    - 2700 * (X 0) ^ 4 * (X 2) ^ 6
    + 15228 * (X 0) ^ 4 * (X 2) ^ 5
    - 18468 * (X 0) ^ 4 * (X 2) ^ 4
    - 8748 * (X 0) ^ 4 * (X 2) ^ 3
    + 297 * (X 0) ^ 3 * (X 2) ^ 7
    + 1350 * (X 0) ^ 3 * (X 2) ^ 6
    - 13932 * (X 0) ^ 3 * (X 2) ^ 5
    + 15660 * (X 0) ^ 3 * (X 2) ^ 4
    + 15930 * (X 0) ^ 3 * (X 2) ^ 3
    + 6480 * (X 0) ^ 3 * (X 2) ^ 2
    - 1701 * (X 0) ^ 3 * (X 2)
    - 675 * (X 0) ^ 2 * (X 2) ^ 7
    + 3807 * (X 0) ^ 2 * (X 2) ^ 6
    - 4617 * (X 0) ^ 2 * (X 2) ^ 5
    - 2187 * (X 0) ^ 2 * (X 2) ^ 4
    + 36 * (X 0) * (X 2) ^ 8
    - 216 * (X 0) * (X 2) ^ 7
    + 324 * (X 0) * (X 2) ^ 6
/-- `(2 a₁ a₂)/z`. -/
public noncomputable def redH3_c3p : MvPolynomial (Fin 3) ℚ :=
  - 354294 * (X 0) ^ 15 * (X 2) ^ 9
    + 3188646 * (X 0) ^ 15 * (X 2) ^ 8
    - 9565938 * (X 0) ^ 15 * (X 2) ^ 7
    + 9565938 * (X 0) ^ 15 * (X 2) ^ 6
    + 3031182 * (X 0) ^ 14 * (X 2) ^ 9
    - 26453952 * (X 0) ^ 14 * (X 2) ^ 8
    + 74401740 * (X 0) ^ 14 * (X 2) ^ 7
    - 59521392 * (X 0) ^ 14 * (X 2) ^ 6
    - 22320522 * (X 0) ^ 14 * (X 2) ^ 5
    + 944784 * (X 0) ^ 13 * (X 2) ^ 10
    - 17154828 * (X 0) ^ 13 * (X 2) ^ 9
    + 98743050 * (X 0) ^ 13 * (X 2) ^ 8
    - 218363202 * (X 0) ^ 13 * (X 2) ^ 7
    + 117389412 * (X 0) ^ 13 * (X 2) ^ 6
    + 96367968 * (X 0) ^ 13 * (X 2) ^ 5
    + 35075106 * (X 0) ^ 13 * (X 2) ^ 4
    - 9565938 * (X 0) ^ 13 * (X 2) ^ 3
    - 11468628 * (X 0) ^ 12 * (X 2) ^ 10
    + 108384804 * (X 0) ^ 12 * (X 2) ^ 9
    - 349656102 * (X 0) ^ 12 * (X 2) ^ 8
    + 393240096 * (X 0) ^ 12 * (X 2) ^ 7
    + 12242826 * (X 0) ^ 12 * (X 2) ^ 6
    - 101485548 * (X 0) ^ 12 * (X 2) ^ 5
    - 80424738 * (X 0) ^ 12 * (X 2) ^ 4
    + 4251528 * (X 0) ^ 12 * (X 2) ^ 3
    + 9565938 * (X 0) ^ 12 * (X 2) ^ 2
    + 275562 * (X 0) ^ 11 * (X 2) ^ 11
    + 46690992 * (X 0) ^ 11 * (X 2) ^ 10
    - 409222692 * (X 0) ^ 11 * (X 2) ^ 9
    + 1092445866 * (X 0) ^ 11 * (X 2) ^ 8
    - 677331396 * (X 0) ^ 11 * (X 2) ^ 7
    - 541715526 * (X 0) ^ 11 * (X 2) ^ 6
    - 192381642 * (X 0) ^ 11 * (X 2) ^ 5
    + 53144100 * (X 0) ^ 11 * (X 2) ^ 4
    + 2200122 * (X 0) ^ 10 * (X 2) ^ 11
    - 107690796 * (X 0) ^ 10 * (X 2) ^ 10
    + 781972056 * (X 0) ^ 10 * (X 2) ^ 9
    - 1843282332 * (X 0) ^ 10 * (X 2) ^ 8
    + 772382790 * (X 0) ^ 10 * (X 2) ^ 7
    + 1073773260 * (X 0) ^ 10 * (X 2) ^ 6
    + 854793324 * (X 0) ^ 10 * (X 2) ^ 5
    - 71094996 * (X 0) ^ 10 * (X 2) ^ 4
    - 89990676 * (X 0) ^ 10 * (X 2) ^ 3
    - 787320 * (X 0) ^ 9 * (X 2) ^ 12
    - 27694710 * (X 0) ^ 9 * (X 2) ^ 11
    + 331078266 * (X 0) ^ 9 * (X 2) ^ 10
    - 1218463722 * (X 0) ^ 9 * (X 2) ^ 9
    + 1556057790 * (X 0) ^ 9 * (X 2) ^ 8
    + 65697480 * (X 0) ^ 9 * (X 2) ^ 7
    - 502728606 * (X 0) ^ 9 * (X 2) ^ 6
    - 927777888 * (X 0) ^ 9 * (X 2) ^ 5
    - 87904278 * (X 0) ^ 9 * (X 2) ^ 4
    + 119712006 * (X 0) ^ 9 * (X 2) ^ 3
    + 55978452 * (X 0) ^ 9 * (X 2) ^ 2
    - 7440174 * (X 0) ^ 9 * (X 2)
    + 10130184 * (X 0) ^ 8 * (X 2) ^ 12
    + 37463310 * (X 0) ^ 8 * (X 2) ^ 11
    - 795807018 * (X 0) ^ 8 * (X 2) ^ 10
    + 2436748110 * (X 0) ^ 8 * (X 2) ^ 9
    - 1390968450 * (X 0) ^ 8 * (X 2) ^ 8
    - 1414905894 * (X 0) ^ 8 * (X 2) ^ 7
    - 1122600222 * (X 0) ^ 8 * (X 2) ^ 6
    + 153330570 * (X 0) ^ 8 * (X 2) ^ 5
    + 131443074 * (X 0) ^ 8 * (X 2) ^ 4
    - 572994 * (X 0) ^ 7 * (X 2) ^ 13
    - 37346184 * (X 0) ^ 7 * (X 2) ^ 12
    + 172929978 * (X 0) ^ 7 * (X 2) ^ 11
    + 451789002 * (X 0) ^ 7 * (X 2) ^ 10
    - 2709652176 * (X 0) ^ 7 * (X 2) ^ 9
    + 1614386538 * (X 0) ^ 7 * (X 2) ^ 8
    + 1993995792 * (X 0) ^ 7 * (X 2) ^ 7
    + 2526636726 * (X 0) ^ 7 * (X 2) ^ 6
    + 114143904 * (X 0) ^ 7 * (X 2) ^ 5
    - 431923752 * (X 0) ^ 7 * (X 2) ^ 4
    - 167226768 * (X 0) ^ 7 * (X 2) ^ 3
    + 20667150 * (X 0) ^ 7 * (X 2) ^ 2
    + 4453218 * (X 0) ^ 6 * (X 2) ^ 13
    + 31638600 * (X 0) ^ 6 * (X 2) ^ 12
    - 397465380 * (X 0) ^ 6 * (X 2) ^ 11
    + 771160986 * (X 0) ^ 6 * (X 2) ^ 10
    + 624720924 * (X 0) ^ 6 * (X 2) ^ 9
    - 1122228432 * (X 0) ^ 6 * (X 2) ^ 8
    - 1298990520 * (X 0) ^ 6 * (X 2) ^ 7
    - 1506787596 * (X 0) ^ 6 * (X 2) ^ 6
    - 259480260 * (X 0) ^ 6 * (X 2) ^ 5
    + 256252248 * (X 0) ^ 6 * (X 2) ^ 4
    + 285744672 * (X 0) ^ 6 * (X 2) ^ 3
    + 12715218 * (X 0) ^ 6 * (X 2) ^ 2
    - 11849166 * (X 0) ^ 6 * (X 2)
    - 151632 * (X 0) ^ 5 * (X 2) ^ 14
    - 9267534 * (X 0) ^ 5 * (X 2) ^ 13
    + 47185740 * (X 0) ^ 5 * (X 2) ^ 12
    + 81372438 * (X 0) ^ 5 * (X 2) ^ 11
    - 611574138 * (X 0) ^ 5 * (X 2) ^ 10
    + 408123360 * (X 0) ^ 5 * (X 2) ^ 9
    + 443118276 * (X 0) ^ 5 * (X 2) ^ 8
    + 550352718 * (X 0) ^ 5 * (X 2) ^ 7
    + 8746542 * (X 0) ^ 5 * (X 2) ^ 6
    - 104070582 * (X 0) ^ 5 * (X 2) ^ 5
    - 37082772 * (X 0) ^ 5 * (X 2) ^ 4
    + 4408992 * (X 0) ^ 5 * (X 2) ^ 3
    + 700812 * (X 0) ^ 4 * (X 2) ^ 14
    + 1638306 * (X 0) ^ 4 * (X 2) ^ 13
    - 47595924 * (X 0) ^ 4 * (X 2) ^ 12
    + 152413974 * (X 0) ^ 4 * (X 2) ^ 11
    - 96123996 * (X 0) ^ 4 * (X 2) ^ 10
    - 81431730 * (X 0) ^ 4 * (X 2) ^ 9
    - 64394028 * (X 0) ^ 4 * (X 2) ^ 8
    + 11927898 * (X 0) ^ 4 * (X 2) ^ 7
    + 8293104 * (X 0) ^ 4 * (X 2) ^ 6
    - 17010 * (X 0) ^ 3 * (X 2) ^ 15
    - 599238 * (X 0) ^ 3 * (X 2) ^ 14
    + 6000156 * (X 0) ^ 3 * (X 2) ^ 13
    - 17103312 * (X 0) ^ 3 * (X 2) ^ 12
    + 12417300 * (X 0) ^ 3 * (X 2) ^ 11
    + 6657228 * (X 0) ^ 3 * (X 2) ^ 10
    + 2375082 * (X 0) ^ 3 * (X 2) ^ 9
    - 931662 * (X 0) ^ 3 * (X 2) ^ 8
    + 35478 * (X 0) ^ 2 * (X 2) ^ 15
    - 312336 * (X 0) ^ 2 * (X 2) ^ 14
    + 895212 * (X 0) ^ 2 * (X 2) ^ 13
    - 769824 * (X 0) ^ 2 * (X 2) ^ 12
    - 188082 * (X 0) ^ 2 * (X 2) ^ 11
    - 648 * (X 0) * (X 2) ^ 16
    + 5832 * (X 0) * (X 2) ^ 15
    - 17496 * (X 0) * (X 2) ^ 14
    + 17496 * (X 0) * (X 2) ^ 13
/-- `(a₂²)/z`. -/
public noncomputable def redH3_c4p : MvPolynomial (Fin 3) ℚ :=
  59049 * (X 0) ^ 14 * (X 2) ^ 9
    - 708588 * (X 0) ^ 14 * (X 2) ^ 8
    + 3188646 * (X 0) ^ 14 * (X 2) ^ 7
    - 6377292 * (X 0) ^ 14 * (X 2) ^ 6
    + 4782969 * (X 0) ^ 14 * (X 2) ^ 5
    - 328050 * (X 0) ^ 13 * (X 2) ^ 9
    + 3818502 * (X 0) ^ 13 * (X 2) ^ 8
    - 16297524 * (X 0) ^ 13 * (X 2) ^ 7
    + 29052108 * (X 0) ^ 13 * (X 2) ^ 6
    - 13817466 * (X 0) ^ 13 * (X 2) ^ 5
    - 9565938 * (X 0) ^ 13 * (X 2) ^ 4
    - 236196 * (X 0) ^ 12 * (X 2) ^ 10
    + 3289977 * (X 0) ^ 12 * (X 2) ^ 9
    - 17894034 * (X 0) ^ 12 * (X 2) ^ 8
    + 46235367 * (X 0) ^ 12 * (X 2) ^ 7
    - 51333264 * (X 0) ^ 12 * (X 2) ^ 6
    + 4664871 * (X 0) ^ 12 * (X 2) ^ 5
    + 20194758 * (X 0) ^ 12 * (X 2) ^ 4
    + 4782969 * (X 0) ^ 12 * (X 2) ^ 3
    + 1968300 * (X 0) ^ 11 * (X 2) ^ 10
    - 22911012 * (X 0) ^ 11 * (X 2) ^ 9
    + 97785144 * (X 0) ^ 11 * (X 2) ^ 8
    - 174312648 * (X 0) ^ 11 * (X 2) ^ 7
    + 82904796 * (X 0) ^ 11 * (X 2) ^ 6
    + 57395628 * (X 0) ^ 11 * (X 2) ^ 5
    + 91854 * (X 0) ^ 10 * (X 2) ^ 11
    - 6269400 * (X 0) ^ 10 * (X 2) ^ 10
    + 63278658 * (X 0) ^ 10 * (X 2) ^ 9
    - 245460132 * (X 0) ^ 10 * (X 2) ^ 8
    + 375604128 * (X 0) ^ 10 * (X 2) ^ 7
    - 62513208 * (X 0) ^ 10 * (X 2) ^ 6
    - 211513518 * (X 0) ^ 10 * (X 2) ^ 5
    - 71567388 * (X 0) ^ 10 * (X 2) ^ 4
    + 7440174 * (X 0) ^ 10 * (X 2) ^ 3
    - 1895400 * (X 0) ^ 9 * (X 2) ^ 11
    + 26290656 * (X 0) ^ 9 * (X 2) ^ 10
    - 140427270 * (X 0) ^ 9 * (X 2) ^ 9
    + 344348982 * (X 0) ^ 9 * (X 2) ^ 8
    - 317195190 * (X 0) ^ 9 * (X 2) ^ 7
    - 95838714 * (X 0) ^ 9 * (X 2) ^ 6
    + 163959390 * (X 0) ^ 9 * (X 2) ^ 5
    + 142465554 * (X 0) ^ 9 * (X 2) ^ 4
    + 12636486 * (X 0) ^ 9 * (X 2) ^ 3
    - 7440174 * (X 0) ^ 9 * (X 2) ^ 2
    + 271188 * (X 0) ^ 8 * (X 2) ^ 12
    + 6168798 * (X 0) ^ 8 * (X 2) ^ 11
    - 91714032 * (X 0) ^ 8 * (X 2) ^ 10
    + 400339098 * (X 0) ^ 8 * (X 2) ^ 9
    - 649958904 * (X 0) ^ 8 * (X 2) ^ 8
    + 115696674 * (X 0) ^ 8 * (X 2) ^ 7
    + 382637520 * (X 0) ^ 8 * (X 2) ^ 6
    + 133568838 * (X 0) ^ 8 * (X 2) ^ 5
    - 14880348 * (X 0) ^ 8 * (X 2) ^ 4
    - 2211300 * (X 0) ^ 7 * (X 2) ^ 12
    + 8826732 * (X 0) ^ 7 * (X 2) ^ 11
    + 75197808 * (X 0) ^ 7 * (X 2) ^ 10
    - 510136704 * (X 0) ^ 7 * (X 2) ^ 9
    + 856303812 * (X 0) ^ 7 * (X 2) ^ 8
    + 97793892 * (X 0) ^ 7 * (X 2) ^ 7
    - 655837560 * (X 0) ^ 7 * (X 2) ^ 6
    - 569862216 * (X 0) ^ 7 * (X 2) ^ 5
    - 50545944 * (X 0) ^ 7 * (X 2) ^ 4
    + 29760696 * (X 0) ^ 7 * (X 2) ^ 3
    + 123201 * (X 0) ^ 6 * (X 2) ^ 13
    + 4026996 * (X 0) ^ 6 * (X 2) ^ 12
    - 45679140 * (X 0) ^ 6 * (X 2) ^ 11
    + 133716096 * (X 0) ^ 6 * (X 2) ^ 10
    - 8931708 * (X 0) ^ 6 * (X 2) ^ 9
    - 352171152 * (X 0) ^ 6 * (X 2) ^ 8
    - 20594250 * (X 0) ^ 6 * (X 2) ^ 7
    + 352039932 * (X 0) ^ 6 * (X 2) ^ 6
    + 504115164 * (X 0) ^ 6 * (X 2) ^ 5
    + 153177480 * (X 0) ^ 6 * (X 2) ^ 4
    - 12203460 * (X 0) ^ 6 * (X 2) ^ 3
    - 22044960 * (X 0) ^ 6 * (X 2) ^ 2
    + 2893401 * (X 0) ^ 6 * (X 2)
    - 595350 * (X 0) ^ 5 * (X 2) ^ 13
    + 2701674 * (X 0) ^ 5 * (X 2) ^ 12
    + 16686810 * (X 0) ^ 5 * (X 2) ^ 11
    - 123768162 * (X 0) ^ 5 * (X 2) ^ 10
    + 212284800 * (X 0) ^ 5 * (X 2) ^ 9
    + 23208444 * (X 0) ^ 5 * (X 2) ^ 8
    - 163959390 * (X 0) ^ 5 * (X 2) ^ 7
    - 142465554 * (X 0) ^ 5 * (X 2) ^ 6
    - 12636486 * (X 0) ^ 5 * (X 2) ^ 5
    + 7440174 * (X 0) ^ 5 * (X 2) ^ 4
    + 21384 * (X 0) ^ 4 * (X 2) ^ 14
    + 424521 * (X 0) ^ 4 * (X 2) ^ 13
    - 6533298 * (X 0) ^ 4 * (X 2) ^ 12
    + 28747143 * (X 0) ^ 4 * (X 2) ^ 11
    - 46847484 * (X 0) ^ 4 * (X 2) ^ 10
    + 8397351 * (X 0) ^ 4 * (X 2) ^ 9
    + 27595566 * (X 0) ^ 4 * (X 2) ^ 8
    + 9716841 * (X 0) ^ 4 * (X 2) ^ 7
    - 1102248 * (X 0) ^ 4 * (X 2) ^ 6
    - 48600 * (X 0) ^ 3 * (X 2) ^ 14
    + 565704 * (X 0) ^ 3 * (X 2) ^ 13
    - 2414448 * (X 0) ^ 3 * (X 2) ^ 12
    + 4304016 * (X 0) ^ 3 * (X 2) ^ 11
    - 2047032 * (X 0) ^ 3 * (X 2) ^ 10
    - 1417176 * (X 0) ^ 3 * (X 2) ^ 9
    + 1296 * (X 0) ^ 2 * (X 2) ^ 15
    - 15552 * (X 0) ^ 2 * (X 2) ^ 14
    + 69984 * (X 0) ^ 2 * (X 2) ^ 13
    - 139968 * (X 0) ^ 2 * (X 2) ^ 12
    + 104976 * (X 0) ^ 2 * (X 2) ^ 11

public theorem redH3_Y_decomp :
    redH3 = redH3_a0 + redH3_a1 * (X 1) + redH3_a2 * (X 1) ^ 2 := by
  unfold redH3 redH3_a0 redH3_a1 redH3_a2
  ring

public theorem redH3_c3p_spec :
    (X 2) * redH3_c3p = 2 * redH3_a1 * redH3_a2 := by
  unfold redH3_c3p redH3_a1 redH3_a2
  ring

public theorem redH3_c4p_spec :
    (X 2) * redH3_c4p = redH3_a2 ^ 2 := by
  unfold redH3_c4p redH3_a2
  ring

public noncomputable def quotH3sq : MvPolynomial (Fin 3) ℚ :=
  redH3_c3p + redH3_c4p * ((X 1) - 1)

/-- Structural remainder of `redH3²` (`Y`-degree ≤ 2). -/
public noncomputable def redH3sq : MvPolynomial (Fin 3) ℚ :=
  redH3_a0 ^ 2 + (2 * redH3_a0 * redH3_a1) * (X 1)
    + (redH3_a1 ^ 2 + 2 * redH3_a0 * redH3_a2) * (X 1) ^ 2
    + redH3_c3p * y3c + redH3_c4p * y4c

/-- `redH3² ≡ redH3sq (mod gAff)` by Y-split (no monolithic bivariate `ring`). -/
public theorem redH3_sq_mod :
    redH3 ^ 2 = quotH3sq * gAff + redH3sq := by
  rw [redH3_Y_decomp, Ydeg2_sq_expand]
  have hc3 := redH3_c3p_spec
  have hc4 := redH3_c4p_spec
  have hhigh := high_Y34_reduce redH3_c3p redH3_c4p
  -- Connect high-power summands to the factored form via `c₃p`/`c₄p` specs
  have hconn :
      redH3_a0 ^ 2 + (2 * redH3_a0 * redH3_a1) * (X 1)
          + (redH3_a1 ^ 2 + 2 * redH3_a0 * redH3_a2) * (X 1) ^ 2
          + (2 * redH3_a1 * redH3_a2) * (X 1) ^ 3 + (redH3_a2 ^ 2) * (X 1) ^ 4
        = redH3_a0 ^ 2 + (2 * redH3_a0 * redH3_a1) * (X 1)
          + (redH3_a1 ^ 2 + 2 * redH3_a0 * redH3_a2) * (X 1) ^ 2
          + ((X 2) * redH3_c3p) * (X 1) ^ 3 + ((X 2) * redH3_c4p) * (X 1) ^ 4 := by
    rw [hc3, hc4]
  rw [hconn]
  have hhigh' :
      redH3_a0 ^ 2 + (2 * redH3_a0 * redH3_a1) * (X 1)
          + (redH3_a1 ^ 2 + 2 * redH3_a0 * redH3_a2) * (X 1) ^ 2
          + ((X 2) * redH3_c3p) * (X 1) ^ 3 + ((X 2) * redH3_c4p) * (X 1) ^ 4
        = redH3_a0 ^ 2 + (2 * redH3_a0 * redH3_a1) * (X 1)
          + (redH3_a1 ^ 2 + 2 * redH3_a0 * redH3_a2) * (X 1) ^ 2
          + ((X 2) * redH3_c3p * (X 1) ^ 3 + (X 2) * redH3_c4p * (X 1) ^ 4) := by
    ring
  rw [hhigh', hhigh]
  unfold quotH3sq redH3sq
  ring

public theorem gAff_dvd_redH3_sq_sub : gAff ∣ redH3 ^ 2 - redH3sq :=
  dvd_sub_of_mod redH3_sq_mod

/-! ## `redTheta²` by Y-split -/

public noncomputable def redTheta_a0 : MvPolynomial (Fin 3) ℚ :=
  - 81 * (X 0) ^ 6 * (X 2) ^ 5
    + 622 * (X 0) ^ 6 * (X 2) ^ 4
    + 477 * (X 0) ^ 6 * (X 2) ^ 3
    + 81 * (X 0) ^ 6 * (X 2)
    - 216 * (X 0) ^ 5 * (X 2) ^ 5
    - 108 * (X 0) ^ 5 * (X 2) ^ 4
    + 243 * (X 0) ^ 4 * (X 2) ^ 6
    - 629 * (X 0) ^ 4 * (X 2) ^ 5
    - 411 * (X 0) ^ 4 * (X 2) ^ 4
    - 207 * (X 0) ^ 4 * (X 2) ^ 3
    + 135 * (X 0) ^ 4 * (X 2) ^ 2
    - 392 * (X 0) ^ 3 * (X 2) ^ 6
    + 667 * (X 0) ^ 3 * (X 2) ^ 5
    + 311 * (X 0) ^ 3 * (X 2) ^ 4
    + 495 * (X 0) ^ 3 * (X 2) ^ 3
    - 299 * (X 0) ^ 3 * (X 2) ^ 2
    - 126 * (X 0) ^ 3 * (X 2)
    - 99 * (X 0) ^ 2 * (X 2) ^ 7
    + 925 * (X 0) ^ 2 * (X 2) ^ 6
    + 312 * (X 0) ^ 2 * (X 2) ^ 5
    + 201 * (X 0) ^ 2 * (X 2) ^ 4
    - 162 * (X 0) ^ 2 * (X 2) ^ 3
    + 192 * (X 0) * (X 2) ^ 7
    - 1363 * (X 0) * (X 2) ^ 6
    - 578 * (X 0) * (X 2) ^ 5
    - 684 * (X 0) * (X 2) ^ 4
    + 434 * (X 0) * (X 2) ^ 3
    + 123 * (X 0) * (X 2) ^ 2
    + (X 2) ^ 8
    - 110 * (X 2) ^ 7
    + 675 * (X 2) ^ 6
    + 318 * (X 2) ^ 5
    + 497 * (X 2) ^ 4
    - 272 * (X 2) ^ 3
    - 117 * (X 2) ^ 2
    + 1
public noncomputable def redTheta_a1 : MvPolynomial (Fin 3) ℚ :=
  27 * (X 0) ^ 5 * (X 2) ^ 5
    - 81 * (X 0) ^ 5 * (X 2) ^ 4
    + 6 * (X 0) ^ 4 * (X 2) ^ 5
    - 36 * (X 0) ^ 4 * (X 2) ^ 4
    + 54 * (X 0) ^ 4 * (X 2) ^ 3
    - 126 * (X 0) ^ 3 * (X 2) ^ 6
    + 604 * (X 0) ^ 3 * (X 2) ^ 5
    - 581 * (X 0) ^ 3 * (X 2) ^ 4
    - 255 * (X 0) ^ 3 * (X 2) ^ 3
    - 135 * (X 0) ^ 3 * (X 2) ^ 2
    + 81 * (X 0) ^ 3 * (X 2)
    + 264 * (X 0) ^ 2 * (X 2) ^ 6
    - 744 * (X 0) ^ 2 * (X 2) ^ 5
    - 144 * (X 0) ^ 2 * (X 2) ^ 4
    + 51 * (X 0) * (X 2) ^ 7
    - 778 * (X 0) * (X 2) ^ 6
    + 1676 * (X 0) * (X 2) ^ 5
    + 522 * (X 0) * (X 2) ^ 4
    + 300 * (X 0) * (X 2) ^ 3
    - 225 * (X 0) * (X 2) ^ 2
    - 54 * (X 2) ^ 7
    + 625 * (X 2) ^ 6
    - 1201 * (X 2) ^ 5
    - 422 * (X 2) ^ 4
    - 558 * (X 2) ^ 3
    + 353 * (X 2) ^ 2
    + 129 * (X 2)
public noncomputable def redTheta_a2 : MvPolynomial (Fin 3) ℚ :=
  9 * (X 0) ^ 4 * (X 2) ^ 5
    - 54 * (X 0) ^ 4 * (X 2) ^ 4
    + 81 * (X 0) ^ 4 * (X 2) ^ 3
    + 25 * (X 0) ^ 3 * (X 2) ^ 5
    - 141 * (X 0) ^ 3 * (X 2) ^ 4
    + 171 * (X 0) ^ 3 * (X 2) ^ 3
    + 81 * (X 0) ^ 3 * (X 2) ^ 2
    + 21 * (X 0) ^ 2 * (X 2) ^ 6
    - 126 * (X 0) ^ 2 * (X 2) ^ 5
    + 189 * (X 0) ^ 2 * (X 2) ^ 4
    - 100 * (X 0) * (X 2) ^ 6
    + 564 * (X 0) * (X 2) ^ 5
    - 684 * (X 0) * (X 2) ^ 4
    - 324 * (X 0) * (X 2) ^ 3
    - 6 * (X 2) ^ 7
    + 152 * (X 2) ^ 6
    - 669 * (X 2) ^ 5
    + 580 * (X 2) ^ 4
    + 590 * (X 2) ^ 3
    + 240 * (X 2) ^ 2
    - 63 * (X 2)
public noncomputable def redTheta_c3p : MvPolynomial (Fin 3) ℚ :=
  486 * (X 0) ^ 9 * (X 2) ^ 9
    - 4374 * (X 0) ^ 9 * (X 2) ^ 8
    + 13122 * (X 0) ^ 9 * (X 2) ^ 7
    - 13122 * (X 0) ^ 9 * (X 2) ^ 6
    + 1458 * (X 0) ^ 8 * (X 2) ^ 9
    - 12960 * (X 0) ^ 8 * (X 2) ^ 8
    + 37908 * (X 0) ^ 8 * (X 2) ^ 7
    - 34992 * (X 0) ^ 8 * (X 2) ^ 6
    - 4374 * (X 0) ^ 8 * (X 2) ^ 5
    - 1134 * (X 0) ^ 7 * (X 2) ^ 10
    + 14574 * (X 0) ^ 7 * (X 2) ^ 9
    - 68976 * (X 0) ^ 7 * (X 2) ^ 8
    + 140292 * (X 0) ^ 7 * (X 2) ^ 7
    - 95580 * (X 0) ^ 7 * (X 2) ^ 6
    - 12636 * (X 0) ^ 7 * (X 2) ^ 5
    - 21870 * (X 0) ^ 7 * (X 2) ^ 4
    + 13122 * (X 0) ^ 7 * (X 2) ^ 3
    - 6696 * (X 0) ^ 6 * (X 2) ^ 10
    + 67460 * (X 0) ^ 6 * (X 2) ^ 9
    - 236638 * (X 0) ^ 6 * (X 2) ^ 8
    + 298368 * (X 0) ^ 6 * (X 2) ^ 7
    + 13878 * (X 0) ^ 6 * (X 2) ^ 6
    - 139212 * (X 0) ^ 6 * (X 2) ^ 5
    - 110322 * (X 0) ^ 6 * (X 2) ^ 4
    + 5832 * (X 0) ^ 6 * (X 2) ^ 3
    + 13122 * (X 0) ^ 6 * (X 2) ^ 2
    - 4698 * (X 0) ^ 5 * (X 2) ^ 11
    + 58788 * (X 0) ^ 5 * (X 2) ^ 10
    - 260214 * (X 0) ^ 5 * (X 2) ^ 9
    + 439344 * (X 0) ^ 5 * (X 2) ^ 8
    - 67392 * (X 0) ^ 5 * (X 2) ^ 7
    - 313794 * (X 0) ^ 5 * (X 2) ^ 6
    - 99144 * (X 0) ^ 5 * (X 2) ^ 5
    + 4374 * (X 0) ^ 5 * (X 2) ^ 4
    + 37794 * (X 0) ^ 4 * (X 2) ^ 11
    - 394648 * (X 0) ^ 4 * (X 2) ^ 10
    + 1454264 * (X 0) ^ 4 * (X 2) ^ 9
    - 2003376 * (X 0) ^ 4 * (X 2) ^ 8
    + 137334 * (X 0) ^ 4 * (X 2) ^ 7
    + 932328 * (X 0) ^ 4 * (X 2) ^ 6
    + 611388 * (X 0) ^ 4 * (X 2) ^ 5
    + 22032 * (X 0) ^ 4 * (X 2) ^ 4
    - 74844 * (X 0) ^ 4 * (X 2) ^ 3
    + 3654 * (X 0) ^ 3 * (X 2) ^ 12
    - 146580 * (X 0) ^ 3 * (X 2) ^ 11
    + 1137972 * (X 0) ^ 3 * (X 2) ^ 10
    - 3248740 * (X 0) ^ 3 * (X 2) ^ 9
    + 2974894 * (X 0) ^ 3 * (X 2) ^ 8
    + 850440 * (X 0) ^ 3 * (X 2) ^ 7
    - 370798 * (X 0) ^ 3 * (X 2) ^ 6
    - 1358208 * (X 0) ^ 3 * (X 2) ^ 5
    - 120582 * (X 0) ^ 3 * (X 2) ^ 4
    + 164214 * (X 0) ^ 3 * (X 2) ^ 3
    + 76788 * (X 0) ^ 3 * (X 2) ^ 2
    - 10206 * (X 0) ^ 3 * (X 2)
    - 15636 * (X 0) ^ 2 * (X 2) ^ 12
    + 342170 * (X 0) ^ 2 * (X 2) ^ 11
    - 2088586 * (X 0) ^ 2 * (X 2) ^ 10
    + 4596498 * (X 0) ^ 2 * (X 2) ^ 9
    - 1989726 * (X 0) ^ 2 * (X 2) ^ 8
    - 2339058 * (X 0) ^ 2 * (X 2) ^ 7
    - 1857222 * (X 0) ^ 2 * (X 2) ^ 6
    + 238950 * (X 0) ^ 2 * (X 2) ^ 5
    + 212706 * (X 0) ^ 2 * (X 2) ^ 4
    - 612 * (X 0) * (X 2) ^ 13
    + 35640 * (X 0) * (X 2) ^ 12
    - 510774 * (X 0) * (X 2) ^ 11
    + 2622436 * (X 0) * (X 2) ^ 10
    - 5020036 * (X 0) * (X 2) ^ 9
    + 1319616 * (X 0) * (X 2) ^ 8
    + 2389054 * (X 0) * (X 2) ^ 7
    + 3576702 * (X 0) * (X 2) ^ 6
    + 156576 * (X 0) * (X 2) ^ 5
    - 592488 * (X 0) * (X 2) ^ 4
    - 229392 * (X 0) * (X 2) ^ 3
    + 28350 * (X 0) * (X 2) ^ 2
    + 648 * (X 2) ^ 13
    - 23916 * (X 2) ^ 12
    + 276664 * (X 2) ^ 11
    - 1258930 * (X 2) ^ 10
    + 2146626 * (X 2) ^ 9
    - 290812 * (X 2) ^ 8
    - 747528 * (X 2) ^ 7
    - 2233568 * (X 2) ^ 6
    - 472796 * (X 2) ^ 5
    + 351512 * (X 2) ^ 4
    + 391968 * (X 2) ^ 3
    + 17442 * (X 2) ^ 2
    - 16254 * (X 2)
public noncomputable def redTheta_c4p : MvPolynomial (Fin 3) ℚ :=
  81 * (X 0) ^ 8 * (X 2) ^ 9
    - 972 * (X 0) ^ 8 * (X 2) ^ 8
    + 4374 * (X 0) ^ 8 * (X 2) ^ 7
    - 8748 * (X 0) ^ 8 * (X 2) ^ 6
    + 6561 * (X 0) ^ 8 * (X 2) ^ 5
    + 450 * (X 0) ^ 7 * (X 2) ^ 9
    - 5238 * (X 0) ^ 7 * (X 2) ^ 8
    + 22356 * (X 0) ^ 7 * (X 2) ^ 7
    - 39852 * (X 0) ^ 7 * (X 2) ^ 6
    + 18954 * (X 0) ^ 7 * (X 2) ^ 5
    + 13122 * (X 0) ^ 7 * (X 2) ^ 4
    + 378 * (X 0) ^ 6 * (X 2) ^ 10
    - 3911 * (X 0) ^ 6 * (X 2) ^ 9
    + 13362 * (X 0) ^ 6 * (X 2) ^ 8
    - 12393 * (X 0) ^ 6 * (X 2) ^ 7
    - 13554 * (X 0) ^ 6 * (X 2) ^ 6
    + 6399 * (X 0) ^ 6 * (X 2) ^ 5
    + 27702 * (X 0) ^ 6 * (X 2) ^ 4
    + 6561 * (X 0) ^ 6 * (X 2) ^ 3
    - 750 * (X 0) ^ 5 * (X 2) ^ 10
    + 8730 * (X 0) ^ 5 * (X 2) ^ 9
    - 37260 * (X 0) ^ 5 * (X 2) ^ 8
    + 66420 * (X 0) ^ 5 * (X 2) ^ 7
    - 31590 * (X 0) ^ 5 * (X 2) ^ 6
    - 21870 * (X 0) ^ 5 * (X 2) ^ 5
    + 333 * (X 0) ^ 4 * (X 2) ^ 11
    - 6908 * (X 0) ^ 4 * (X 2) ^ 10
    + 50784 * (X 0) ^ 4 * (X 2) ^ 9
    - 167760 * (X 0) ^ 4 * (X 2) ^ 8
    + 228699 * (X 0) ^ 4 * (X 2) ^ 7
    - 16632 * (X 0) ^ 4 * (X 2) ^ 6
    - 153090 * (X 0) ^ 4 * (X 2) ^ 5
    - 6804 * (X 0) ^ 4 * (X 2) ^ 4
    - 10206 * (X 0) ^ 4 * (X 2) ^ 3
    - 4500 * (X 0) ^ 3 * (X 2) ^ 11
    + 58180 * (X 0) ^ 3 * (X 2) ^ 10
    - 287022 * (X 0) ^ 3 * (X 2) ^ 9
    + 640622 * (X 0) ^ 3 * (X 2) ^ 8
    - 515138 * (X 0) ^ 3 * (X 2) ^ 7
    - 186870 * (X 0) ^ 3 * (X 2) ^ 6
    + 224910 * (X 0) ^ 3 * (X 2) ^ 5
    + 195426 * (X 0) ^ 3 * (X 2) ^ 4
    + 17334 * (X 0) ^ 3 * (X 2) ^ 3
    - 10206 * (X 0) ^ 3 * (X 2) ^ 2
    - 252 * (X 0) ^ 2 * (X 2) ^ 12
    + 17896 * (X 0) ^ 2 * (X 2) ^ 11
    - 181470 * (X 0) ^ 2 * (X 2) ^ 10
    + 705300 * (X 0) ^ 2 * (X 2) ^ 9
    - 1081014 * (X 0) ^ 2 * (X 2) ^ 8
    + 183024 * (X 0) ^ 2 * (X 2) ^ 7
    + 603126 * (X 0) ^ 2 * (X 2) ^ 6
    + 211572 * (X 0) ^ 2 * (X 2) ^ 5
    - 23814 * (X 0) ^ 2 * (X 2) ^ 4
    + 1200 * (X 0) * (X 2) ^ 12
    - 37168 * (X 0) * (X 2) ^ 11
    + 313464 * (X 0) * (X 2) ^ 10
    - 1074680 * (X 0) * (X 2) ^ 9
    + 1352936 * (X 0) * (X 2) ^ 8
    + 257592 * (X 0) * (X 2) ^ 7
    - 899640 * (X 0) * (X 2) ^ 6
    - 781704 * (X 0) * (X 2) ^ 5
    - 69336 * (X 0) * (X 2) ^ 4
    + 40824 * (X 0) * (X 2) ^ 3
    + 36 * (X 2) ^ 13
    - 1824 * (X 2) ^ 12
    + 31132 * (X 2) ^ 11
    - 210336 * (X 2) ^ 10
    + 616801 * (X 2) ^ 9
    - 599560 * (X 2) ^ 8
    - 379304 * (X 2) ^ 7
    + 344128 * (X 2) ^ 6
    + 710794 * (X 2) ^ 5
    + 210120 * (X 2) ^ 4
    - 16740 * (X 2) ^ 3
    - 30240 * (X 2) ^ 2
    + 3969 * (X 2)

public theorem redTheta_Y_decomp :
    redTheta = redTheta_a0 + redTheta_a1 * (X 1) + redTheta_a2 * (X 1) ^ 2 := by
  unfold redTheta redTheta_a0 redTheta_a1 redTheta_a2
  ring

public theorem redTheta_c3p_spec :
    (X 2) * redTheta_c3p = 2 * redTheta_a1 * redTheta_a2 := by
  unfold redTheta_c3p redTheta_a1 redTheta_a2
  ring

public theorem redTheta_c4p_spec :
    (X 2) * redTheta_c4p = redTheta_a2 ^ 2 := by
  unfold redTheta_c4p redTheta_a2
  ring

public noncomputable def quotTheta2 : MvPolynomial (Fin 3) ℚ :=
  redTheta_c3p + redTheta_c4p * ((X 1) - 1)

public noncomputable def redTheta2 : MvPolynomial (Fin 3) ℚ :=
  redTheta_a0 ^ 2 + (2 * redTheta_a0 * redTheta_a1) * (X 1)
    + (redTheta_a1 ^ 2 + 2 * redTheta_a0 * redTheta_a2) * (X 1) ^ 2
    + redTheta_c3p * y3c + redTheta_c4p * y4c

public theorem redTheta_sq_mod :
    redTheta ^ 2 = quotTheta2 * gAff + redTheta2 := by
  rw [redTheta_Y_decomp, Ydeg2_sq_expand]
  have hc3 := redTheta_c3p_spec
  have hc4 := redTheta_c4p_spec
  have hhigh := high_Y34_reduce redTheta_c3p redTheta_c4p
  have hconn :
      redTheta_a0 ^ 2 + (2 * redTheta_a0 * redTheta_a1) * (X 1)
          + (redTheta_a1 ^ 2 + 2 * redTheta_a0 * redTheta_a2) * (X 1) ^ 2
          + (2 * redTheta_a1 * redTheta_a2) * (X 1) ^ 3 + (redTheta_a2 ^ 2) * (X 1) ^ 4
        = redTheta_a0 ^ 2 + (2 * redTheta_a0 * redTheta_a1) * (X 1)
          + (redTheta_a1 ^ 2 + 2 * redTheta_a0 * redTheta_a2) * (X 1) ^ 2
          + ((X 2) * redTheta_c3p) * (X 1) ^ 3 + ((X 2) * redTheta_c4p) * (X 1) ^ 4 := by
    rw [hc3, hc4]
  rw [hconn]
  have hhigh' :
      redTheta_a0 ^ 2 + (2 * redTheta_a0 * redTheta_a1) * (X 1)
          + (redTheta_a1 ^ 2 + 2 * redTheta_a0 * redTheta_a2) * (X 1) ^ 2
          + ((X 2) * redTheta_c3p) * (X 1) ^ 3 + ((X 2) * redTheta_c4p) * (X 1) ^ 4
        = redTheta_a0 ^ 2 + (2 * redTheta_a0 * redTheta_a1) * (X 1)
          + (redTheta_a1 ^ 2 + 2 * redTheta_a0 * redTheta_a2) * (X 1) ^ 2
          + ((X 2) * redTheta_c3p * (X 1) ^ 3 + (X 2) * redTheta_c4p * (X 1) ^ 4) := by
    ring
  rw [hhigh', hhigh]
  unfold quotTheta2 redTheta2
  ring

public theorem gAff_dvd_redTheta_sq_sub : gAff ∣ redTheta ^ 2 - redTheta2 :=
  dvd_sub_of_mod redTheta_sq_mod

#print axioms z_mul_Y3_eq
#print axioms z_mul_Y4_eq
#print axioms high_Y34_reduce
#print axioms redH3_Y_decomp
#print axioms redH3_c3p_spec
#print axioms redH3_c4p_spec
#print axioms redH3_sq_mod
#print axioms redTheta_Y_decomp
#print axioms redTheta_c3p_spec
#print axioms redTheta_c4p_spec
#print axioms redTheta_sq_mod
#print axioms gAff_dvd_redH3_sq_sub
#print axioms gAff_dvd_redTheta_sq_sub

end ExplicitUnirational
