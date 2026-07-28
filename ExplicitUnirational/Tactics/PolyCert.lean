/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public meta import Lean

/-!
# `poly_cert`: kernel-checked sparse-polynomial identities in `MvPolynomial (Fin 3) ℚ`

A reflection tactic for large sparse polynomial identities with integer
coefficients, e.g. the Tower-B reduction certificates
`P = Q * gAff + R` with 300–1400 monomials, where `ring` needs minutes to hours.

## Design

* A monomial `X^a * Y^b * z^c` is encoded by the single natural number
  `key = c + a·4096 + b·4096²` (Kronecker substitution).  Key comparison and
  monomial multiplication (`key₁ + key₂`) are then single GMP operations in the
  kernel, which is what makes kernel-side normalization feasible at this size.
* A sparse polynomial is a key-sorted `List (Nat × Int)`; addition is a fueled
  sorted merge (fuel makes it structurally recursive, hence kernel-reducible;
  the fuel-0 fallback keeps the denotation lemma unconditional), and
  multiplication distributes one factor over the other, merging as it goes.
* Monomial multiplication as key addition is only faithful when the per-variable
  digits do not overflow the base 4096.  This is *checked*, not assumed: the
  guard `okMul` is evaluated for every monomial product, and the whole
  computation is `Option`-valued, so the soundness theorem needs no degree
  side conditions.
* The syntactic side: `PExpr` mirrors the goal expression exactly (`X i`,
  numerals, `+`, `-`, unary `-`, `*`, `^`); `PExpr.denote` maps it back, so
  `PExpr.denote e ≡ goal` holds by (kernel-checked) syntactic unfolding, and
  `checkEq e₁ e₂ = true` — evaluated by the kernel, no `native_decide` — plus
  `denote_eq_of_checkEq` closes the goal.

The tactic `poly_cert` expects a goal of the form `lhs = rhs` in
`MvPolynomial (Fin 3) ℚ` built from `X 0`, `X 1`, `X 2`, natural-number
numerals, `+`, `-`, `*`, and `^` with numeral exponents (i.e. what `unfold`
of the certificate definitions produces).  It reifies both sides, checks the
certificate natively first (for fast, informative failure), and closes the
goal with a proof whose only nontrivial obligation is one boolean kernel
computation.
-/

set_option autoImplicit false

namespace ExplicitUnirational

namespace PolyCert

open MvPolynomial

@[expose] public section

/-- Sparse polynomial: key-sorted list of (Kronecker key, coefficient). -/
abbrev Rep := List (Nat × Int)

/-- Merge two key-sorted monomial lists, adding coefficients on equal keys.
The fuel argument makes this structurally recursive; with fuel `0` it falls
back to append, which is still denotation-correct (so the soundness lemma
has no fuel hypothesis), just not sorted. -/
def mergeF : Nat → Rep → Rep → Rep
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, x :: xs, [] => x :: xs
  | f+1, x :: xs, y :: ys =>
    bif x.1.blt y.1 then x :: mergeF f xs (y :: ys)
    else bif y.1.blt x.1 then y :: mergeF f (x :: xs) ys
    else (x.1, x.2 + y.2) :: mergeF f xs ys

/-- Addition of sparse polynomials: merge with plenty of fuel. -/
def addRep (xs ys : Rep) : Rep := mergeF 1000000000 xs ys

/-- Digit-overflow guard for multiplying monomial keys: the `z`- and `X`-digits
of the two keys must sum below the base (the top digit cannot overflow). -/
def okMul (k₁ k₂ : Nat) : Bool :=
  (k₁ % 4096 + k₂ % 4096).blt 4096 && (k₁ / 4096 % 4096 + k₂ / 4096 % 4096).blt 4096

/-- Multiply every monomial of `l` by the monomial `m`, guarding against digit
overflow.  Preserves sortedness (key translation is monotone). -/
def scaleRep? (m : Nat × Int) : Rep → Option Rep
  | [] => some []
  | n :: t =>
    bif okMul m.1 n.1 then
      match scaleRep? m t with
      | some r => some ((m.1 + n.1, m.2 * n.2) :: r)
      | none => none
    else none

/-- Product, distributing the first factor over the second. -/
def mulCore? : Rep → Rep → Option Rep
  | [], _ => some []
  | m :: t, ys =>
    match scaleRep? m ys, mulCore? t ys with
    | some s, some r => some (addRep s r)
    | _, _ => none

/-- Product; puts the shorter factor outside for fewer merge passes. -/
def mulRep? (xs ys : Rep) : Option Rep :=
  bif xs.length.ble ys.length then mulCore? xs ys else mulCore? ys xs

/-- Power by iterated multiplication (exponents here are small). -/
def powRep? (xs : Rep) : Nat → Option Rep
  | 0 => some [(0, 1)]
  | n+1 =>
    match powRep? xs n with
    | some r => mulRep? xs r
    | none => none

/-- Drop zero coefficients (cancellation leaves them behind). -/
def canon : Rep → Rep
  | [] => []
  | m :: t => bif m.2 == 0 then canon t else m :: canon t

/-- Structural equality of monomial lists via GMP-backed `Nat`/`Int` equality. -/
def beqRep : Rep → Rep → Bool
  | [], [] => true
  | x :: xs, y :: ys => x.1 == y.1 && x.2 == y.2 && beqRep xs ys
  | _, _ => false

/-! ## Syntax and denotation -/

/-- Reflected syntax of the goal.  Constructor arguments are chosen so that
`denote` unfolds to a term syntactically equal to the source expression. -/
inductive PExpr where
  | xv (i : Fin 3)
  | zero
  | one
  | nat (n : Nat)
  | add (a b : PExpr)
  | sub (a b : PExpr)
  | neg (a : PExpr)
  | mul (a b : PExpr)
  | pow (a : PExpr) (n : Nat)

/-- Denotation of one monomial: decode the three digits of the key. -/
noncomputable def monD (m : Nat × Int) : MvPolynomial (Fin 3) ℚ :=
  C (m.2 : ℚ) * X 0 ^ (m.1 / 4096 % 4096) * X 1 ^ (m.1 / 4096 / 4096) * X 2 ^ (m.1 % 4096)

/-- Denotation of a sparse polynomial. -/
noncomputable def repD : Rep → MvPolynomial (Fin 3) ℚ
  | [] => 0
  | m :: t => monD m + repD t

/-- Denotation of the reflected syntax; matches the source term on the nose. -/
noncomputable def PExpr.denote : PExpr → MvPolynomial (Fin 3) ℚ
  | .xv i => X i
  | .zero => 0
  | .one => 1
  | .nat n => n
  | .add a b => a.denote + b.denote
  | .sub a b => a.denote - b.denote
  | .neg a => -a.denote
  | .mul a b => a.denote * b.denote
  | .pow a n => a.denote ^ n

/-- Key of the variable with (value of the) index `v`. -/
def xKey : Nat → Nat
  | 0 => 4096
  | 1 => 16777216
  | _ => 1

/-- Evaluate the reflected syntax to a canonical sparse polynomial;
`none` on digit overflow. -/
def PExpr.toRep? : PExpr → Option Rep
  | .xv i => some [(xKey i.val, 1)]
  | .zero => some []
  | .one => some [(0, 1)]
  | .nat n => some [(0, (n : Int))]
  | .add a b =>
    match a.toRep?, b.toRep? with
    | some ra, some rb => some (addRep ra rb)
    | _, _ => none
  | .sub a b =>
    match a.toRep?, b.toRep? with
    | some ra, some rb =>
      match scaleRep? (0, -1) rb with
      | some rb' => some (addRep ra rb')
      | none => none
    | _, _ => none
  | .neg a =>
    match a.toRep? with
    | some ra => scaleRep? (0, -1) ra
    | none => none
  | .mul a b =>
    match a.toRep?, b.toRep? with
    | some ra, some rb => mulRep? ra rb
    | _, _ => none
  | .pow a n =>
    match a.toRep? with
    | some ra => powRep? ra n
    | none => none

/-- The whole certificate check, evaluated by the kernel. -/
def checkEq (e₁ e₂ : PExpr) : Bool :=
  match e₁.toRep?, e₂.toRep? with
  | some r₁, some r₂ => beqRep (canon r₁) (canon r₂)
  | _, _ => false

end

/-! ## Soundness -/

private theorem repD_append (xs ys : Rep) : repD (xs ++ ys) = repD xs + repD ys := by
  induction xs with
  | nil => simp [repD]
  | cons m t ih => simp [repD, ih, add_assoc]

private theorem monD_add_same (k : Nat) (q₁ q₂ : Int) :
    monD (k, q₁ + q₂) = monD (k, q₁) + monD (k, q₂) := by
  simp [monD, add_mul]

private theorem mergeF_sound (f : Nat) (xs ys : Rep) :
    repD (mergeF f xs ys) = repD xs + repD ys := by
  induction f generalizing xs ys with
  | zero => simp [mergeF, repD_append]
  | succ f ih =>
    match xs, ys with
    | [], ys => simp [mergeF, repD]
    | x :: xs, [] => simp [mergeF, repD]
    | x :: xs, y :: ys =>
      simp only [mergeF]
      cases hxy : x.1.blt y.1 with
      | true =>
        simp only [cond_true, repD, ih]
        ring
      | false =>
        cases hyx : y.1.blt x.1 with
        | true =>
          simp only [cond_true, cond_false, repD, ih]
          ring
        | false =>
          have hk : x.1 = y.1 := by
            have h1 : ¬ x.1 < y.1 := fun hl =>
              Bool.noConfusion ((Nat.blt_eq.mpr hl).symm.trans hxy)
            have h2 : ¬ y.1 < x.1 := fun hl =>
              Bool.noConfusion ((Nat.blt_eq.mpr hl).symm.trans hyx)
            omega
          simp only [cond_false, repD, ih, monD_add_same]
          rw [show y = (y.1, y.2) from rfl, ← hk]
          rw [show x = (x.1, x.2) from rfl]
          ring

private theorem addRep_sound (xs ys : Rep) : repD (addRep xs ys) = repD xs + repD ys :=
  mergeF_sound _ xs ys

private theorem monD_mul {k₁ k₂ : Nat} (q₁ q₂ : Int) (h : okMul k₁ k₂ = true) :
    monD (k₁ + k₂, q₁ * q₂) = monD (k₁, q₁) * monD (k₂, q₂) := by
  have h' := h
  simp only [okMul, Bool.and_eq_true, Nat.blt_eq] at h'
  obtain ⟨h1, h2⟩ := h'
  have e1 : (k₁ + k₂) % 4096 = k₁ % 4096 + k₂ % 4096 := by omega
  have e2 : (k₁ + k₂) / 4096 % 4096 = k₁ / 4096 % 4096 + k₂ / 4096 % 4096 := by omega
  have e3 : (k₁ + k₂) / 4096 / 4096 = k₁ / 4096 / 4096 + k₂ / 4096 / 4096 := by omega
  simp only [monD, e1, e2, e3, pow_add, Int.cast_mul, map_mul]
  ring

private theorem scaleRep?_sound (m : Nat × Int) (l : Rep) :
    ∀ r : Rep, scaleRep? m l = some r → repD r = monD m * repD l := by
  induction l with
  | nil =>
    intro r h
    simp only [scaleRep?, Option.some.injEq] at h
    simp [← h, repD]
  | cons n t ih =>
    intro r h
    simp only [scaleRep?] at h
    cases hg : okMul m.1 n.1 with
    | false => rw [hg] at h; simp at h
    | true =>
      rw [hg] at h
      simp only [cond_true] at h
      cases hs : scaleRep? m t with
      | none => rw [hs] at h; simp at h
      | some rt =>
        rw [hs] at h
        simp only [Option.some.injEq] at h
        subst h
        have hmul := monD_mul m.2 n.2 hg
        simp only [repD, ih rt hs, mul_add]
        rw [show m = (m.1, m.2) from rfl, show n = (n.1, n.2) from rfl] at hmul ⊢
        rw [hmul]

private theorem mulCore?_sound (xs ys : Rep) :
    ∀ r : Rep, mulCore? xs ys = some r → repD r = repD xs * repD ys := by
  induction xs with
  | nil =>
    intro r h
    simp only [mulCore?, Option.some.injEq] at h
    simp [← h, repD]
  | cons m t ih =>
    intro r h
    simp only [mulCore?] at h
    cases hs : scaleRep? m ys with
    | none => rw [hs] at h; simp at h
    | some s =>
      cases hc : mulCore? t ys with
      | none => rw [hs, hc] at h; simp at h
      | some rt =>
        rw [hs, hc] at h
        simp only [Option.some.injEq] at h
        subst h
        rw [addRep_sound, scaleRep?_sound m ys s hs, ih rt hc, repD, add_mul]

private theorem mulRep?_sound (xs ys : Rep) :
    ∀ r : Rep, mulRep? xs ys = some r → repD r = repD xs * repD ys := by
  intro r h
  simp only [mulRep?] at h
  cases hl : xs.length.ble ys.length with
  | true => rw [hl] at h; simpa using mulCore?_sound xs ys r h
  | false =>
    rw [hl] at h
    rw [mulCore?_sound ys xs r h, mul_comm]

private theorem monD_one : monD (0, 1) = 1 := by simp [monD]

private theorem powRep?_sound (xs : Rep) (n : Nat) :
    ∀ r : Rep, powRep? xs n = some r → repD r = repD xs ^ n := by
  induction n with
  | zero =>
    intro r h
    simp only [powRep?, Option.some.injEq] at h
    simp [← h, repD, monD_one]
  | succ n ih =>
    intro r h
    simp only [powRep?] at h
    cases hp : powRep? xs n with
    | none => rw [hp] at h; simp at h
    | some rn =>
      rw [hp] at h
      rw [mulRep?_sound xs rn r h, ih rn hp, pow_succ, mul_comm]

private theorem monD_neg_one : monD (0, -1) = -1 := by simp [monD]

private theorem canon_sound (l : Rep) : repD (canon l) = repD l := by
  induction l with
  | nil => rfl
  | cons m t ih =>
    simp only [canon]
    cases hz : m.2 == 0 with
    | false => simp [repD, ih]
    | true =>
      have h0 : m.2 = 0 := eq_of_beq hz
      have hm : monD m = 0 := by
        rw [show m = (m.1, m.2) from rfl, h0]
        simp [monD]
      simp [repD, ih, hm]

private theorem beqRep_sound : ∀ l₁ l₂ : Rep, beqRep l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [beqRep] at h
  | _ :: _, [], h => by simp [beqRep] at h
  | x :: xs, y :: ys, h => by
    simp only [beqRep, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hx : x = y := Prod.ext (eq_of_beq h1) (eq_of_beq h2)
    rw [hx, beqRep_sound xs ys h3]

private theorem toRep?_sound (e : PExpr) :
    ∀ r : Rep, e.toRep? = some r → repD r = e.denote := by
  induction e with
  | xv i =>
    intro r h
    simp only [PExpr.toRep?, Option.some.injEq] at h
    subst h
    show repD [(xKey i.val, 1)] = X i
    fin_cases i <;> simp [repD, monD, xKey]
  | zero =>
    intro r h
    simp only [PExpr.toRep?, Option.some.injEq] at h
    simp [← h, repD, PExpr.denote]
  | one =>
    intro r h
    simp only [PExpr.toRep?, Option.some.injEq] at h
    simp [← h, repD, monD_one, PExpr.denote]
  | nat n =>
    intro r h
    simp only [PExpr.toRep?, Option.some.injEq] at h
    simp [← h, repD, monD, PExpr.denote]
  | add a b iha ihb =>
    intro r h
    simp only [PExpr.toRep?] at h
    cases ha : a.toRep? with
    | none => rw [ha] at h; simp at h
    | some ra =>
      cases hb : b.toRep? with
      | none => rw [ha, hb] at h; simp at h
      | some rb =>
        rw [ha, hb] at h
        simp only [Option.some.injEq] at h
        subst h
        rw [addRep_sound, iha ra ha, ihb rb hb, PExpr.denote]
  | sub a b iha ihb =>
    intro r h
    simp only [PExpr.toRep?] at h
    cases ha : a.toRep? with
    | none => rw [ha] at h; simp at h
    | some ra =>
      cases hb : b.toRep? with
      | none => rw [ha, hb] at h; simp at h
      | some rb =>
        simp only [ha, hb] at h
        cases hsc : scaleRep? (0, -1) rb with
        | none => simp [hsc] at h
        | some rb' =>
          simp only [hsc, Option.some.injEq] at h
          subst h
          rw [addRep_sound, iha ra ha, scaleRep?_sound _ _ _ hsc, ihb rb hb,
            monD_neg_one, PExpr.denote]
          ring
  | neg a iha =>
    intro r h
    simp only [PExpr.toRep?] at h
    cases ha : a.toRep? with
    | none => rw [ha] at h; simp at h
    | some ra =>
      rw [ha] at h
      rw [scaleRep?_sound _ _ _ h, iha ra ha, monD_neg_one, PExpr.denote]
      ring
  | mul a b iha ihb =>
    intro r h
    simp only [PExpr.toRep?] at h
    cases ha : a.toRep? with
    | none => rw [ha] at h; simp at h
    | some ra =>
      cases hb : b.toRep? with
      | none => rw [ha, hb] at h; simp at h
      | some rb =>
        rw [ha, hb] at h
        rw [mulRep?_sound _ _ _ h, iha ra ha, ihb rb hb, PExpr.denote]
  | pow a n iha =>
    intro r h
    simp only [PExpr.toRep?] at h
    cases ha : a.toRep? with
    | none => rw [ha] at h; simp at h
    | some ra =>
      rw [ha] at h
      rw [powRep?_sound _ _ _ h, iha ra ha, PExpr.denote]

/-- Soundness of the certificate check: if the kernel evaluates `checkEq e₁ e₂`
to `true`, the denotations agree.  This is the only theorem the generated
proofs use. -/
public theorem denote_eq_of_checkEq (e₁ e₂ : PExpr) (h : checkEq e₁ e₂ = true) :
    e₁.denote = e₂.denote := by
  unfold checkEq at h
  cases h₁ : e₁.toRep? with
  | none => rw [h₁] at h; simp at h
  | some r₁ =>
    cases h₂ : e₂.toRep? with
    | none => rw [h₁, h₂] at h; simp at h
    | some r₂ =>
      rw [h₁, h₂] at h
      have hc : canon r₁ = canon r₂ := beqRep_sound _ _ h
      calc e₁.denote = repD (canon r₁) := by
            rw [canon_sound, toRep?_sound e₁ r₁ h₁]
        _ = repD (canon r₂) := by rw [hc]
        _ = e₂.denote := by rw [canon_sound, toRep?_sound e₂ r₂ h₂]

/-! ## The tactic -/

meta section

open Lean Meta Elab Tactic

/-- Meta copy of `PolyCert.xKey` (object-level defs are not `meta`). -/
private def xKeyM : Nat → Nat
  | 0 => 4096
  | 1 => 16777216
  | _ => 1

/-- Meta copy of `PolyCert.okMul`. -/
private def okMulM (k₁ k₂ : Nat) : Bool :=
  k₁ % 4096 + k₂ % 4096 < 4096 && k₁ / 4096 % 4096 + k₂ / 4096 % 4096 < 4096

/-- Meta-level mirror of `PExpr`, remembering the original sub-`Expr`s so the
reflected term's denotation unfolds to the goal syntactically. -/
private inductive MExpr where
  | xv (v : Nat) (iE : Expr)
  | zero
  | one
  | nat (n : Nat) (nE : Expr)
  | add (a b : MExpr)
  | sub (a b : MExpr)
  | neg (a : MExpr)
  | mul (a b : MExpr)
  | pow (a : MExpr) (n : Nat) (nE : Expr)

/-- Extract a `Nat` literal, possibly wrapped in `OfNat.ofNat`. -/
private partial def natLitOf? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, l, _]) => natLitOf? l
    | _ => none

/-- Reify a goal-side expression into `MExpr`. -/
private partial def reify (e : Expr) : MetaM MExpr := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return .add (← reify a) (← reify b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return .sub (← reify a) (← reify b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return .mul (← reify a) (← reify b)
  | (``Neg.neg, #[_, _, a]) => return .neg (← reify a)
  | (``HPow.hPow, #[_, _, _, _, a, n]) =>
    let some nv := natLitOf? n
      | throwError "poly_cert: exponent is not a numeral: {n}"
    return .pow (← reify a) nv n
  | (``MvPolynomial.X, args) =>
    let i := args.back!
    let some v := natLitOf? i
      | throwError "poly_cert: variable index is not a numeral: {i}"
    unless v < 3 do throwError "poly_cert: variable index out of range: {v}"
    return .xv v i
  | (``OfNat.ofNat, #[_, l, _]) =>
    let some n := natLitOf? l
      | throwError "poly_cert: numeral literal expected: {l}"
    match n with
    | 0 => return .zero
    | 1 => return .one
    | _ => return .nat n (.lit (.natVal n))
  | _ => throwError "poly_cert: cannot reify subterm{indentExpr e}"

/-- Native evaluation of the certificate (mirrors `PExpr.toRep?` semantically,
via an unordered coefficient map) for fast failure before the kernel runs. -/
private def MExpr.evalMap : MExpr → Option (Std.HashMap Nat Int)
  | .xv v _ => some ((∅ : Std.HashMap Nat Int).insert (xKeyM v) 1)
  | .zero => some ∅
  | .one => some ((∅ : Std.HashMap Nat Int).insert 0 1)
  | .nat n _ => some ((∅ : Std.HashMap Nat Int).insert 0 (n : Int))
  | .add a b => do
    let da ← a.evalMap
    let db ← b.evalMap
    return db.fold (fun d k c => d.insert k (d.getD k 0 + c)) da
  | .sub a b => do
    let da ← a.evalMap
    let db ← b.evalMap
    return db.fold (fun d k c => d.insert k (d.getD k 0 - c)) da
  | .neg a => do
    let da ← a.evalMap
    return da.fold (fun d k c => d.insert k (-c)) ∅
  | .mul a b => do
    let da ← a.evalMap
    let db ← b.evalMap
    let mut r : Std.HashMap Nat Int := ∅
    for (k₁, c₁) in da do
      for (k₂, c₂) in db do
        unless okMulM k₁ k₂ do failure
        r := r.insert (k₁ + k₂) (r.getD (k₁ + k₂) 0 + c₁ * c₂)
    return r
  | .pow a n _ => do
    let da ← a.evalMap
    let mut r : Std.HashMap Nat Int := (∅ : Std.HashMap Nat Int).insert 0 1
    for _ in [0:n] do
      let mut s : Std.HashMap Nat Int := ∅
      for (k₁, c₁) in da do
        for (k₂, c₂) in r do
          unless okMulM k₁ k₂ do failure
          s := s.insert (k₁ + k₂) (s.getD (k₁ + k₂) 0 + c₁ * c₂)
      r := s
    return r

private def dropZeros (d : Std.HashMap Nat Int) : Std.HashMap Nat Int :=
  d.filter fun _ c => c != 0

/-- Build the `PExpr` literal `Expr`, reusing goal sub-`Exprs` for the
`Fin 3` indices and exponents so denotation matches the goal on the nose. -/
private def MExpr.toPExprE : MExpr → Expr
  | .xv _ iE => mkApp (mkConst ``PolyCert.PExpr.xv) iE
  | .zero => mkConst ``PolyCert.PExpr.zero
  | .one => mkConst ``PolyCert.PExpr.one
  | .nat _ nE => mkApp (mkConst ``PolyCert.PExpr.nat) nE
  | .add a b => mkApp2 (mkConst ``PolyCert.PExpr.add) a.toPExprE b.toPExprE
  | .sub a b => mkApp2 (mkConst ``PolyCert.PExpr.sub) a.toPExprE b.toPExprE
  | .neg a => mkApp (mkConst ``PolyCert.PExpr.neg) a.toPExprE
  | .mul a b => mkApp2 (mkConst ``PolyCert.PExpr.mul) a.toPExprE b.toPExprE
  | .pow a _ nE => mkApp2 (mkConst ``PolyCert.PExpr.pow) a.toPExprE nE

/--
`poly_def name := "a.b.c.k a.b.c.k …"` defines
`name : MvPolynomial (Fin 3) ℚ` as the monomial sum
`Σ k · (X 0)^a * (X 1)^b * (X 2)^c` (monomials separated by spaces, negative
coefficients allowed), building the body directly as an `Expr`.

The resulting definition is term-for-term what writing the sum as source
syntax produces — but elaborating such sums costs roughly a second per
monomial at certificate sizes (superlinear in practice; a ~660-monomial
definition set measures ≈ 10 min), while this command is essentially
instant.  Intended for the large sympy-generated certificate polynomials.
-/
elab doc:(Lean.Parser.Command.docComment)? "poly_def " name:ident " := " spec:str : command => do
  Command.liftTermElabM do
    let mvpStx ← `(MvPolynomial (Fin 3) ℚ)
    let elab1 (stx : Term) : Elab.TermElabM Expr := do
      let e ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let mvp ← elab1 mvpStx
    let natTy := mkConst ``Nat
    let hMulInst ← synthInstance (mkApp3 (mkConst ``HMul [0, 0, 0]) mvp mvp mvp)
    let hAddInst ← synthInstance (mkApp3 (mkConst ``HAdd [0, 0, 0]) mvp mvp mvp)
    let hSubInst ← synthInstance (mkApp3 (mkConst ``HSub [0, 0, 0]) mvp mvp mvp)
    let hPowInst ← synthInstance (mkApp3 (mkConst ``HPow [0, 0, 0]) mvp natTy mvp)
    let negInst ← synthInstance (mkApp (mkConst ``Neg [0]) mvp)
    let mkMulE a b := mkApp6 (mkConst ``HMul.hMul [0, 0, 0]) mvp mvp mvp hMulInst a b
    let mkAddE a b := mkApp6 (mkConst ``HAdd.hAdd [0, 0, 0]) mvp mvp mvp hAddInst a b
    let mkSubE a b := mkApp6 (mkConst ``HSub.hSub [0, 0, 0]) mvp mvp mvp hSubInst a b
    let mkPowE a (k : Nat) := mkApp6 (mkConst ``HPow.hPow [0, 0, 0]) mvp natTy mvp
      hPowInst a (mkNatLit k)
    let mkNegE a := mkApp3 (mkConst ``Neg.neg [0]) mvp negInst a
    let mut xArr : Array Expr := #[]
    for i in [0:3] do
      let iStx := Syntax.mkNumLit (toString i)
      xArr := xArr.push (← elab1 (← `((MvPolynomial.X $iStx : $mvpStx))))
    let mut numCache : Std.HashMap Nat Expr := {}
    let mkNum (n : Nat) : Elab.TermElabM Expr := do
      let nStx := Syntax.mkNumLit (toString n)
      elab1 (← `(($nStx : $mvpStx)))
    let mut acc : Option Expr := none
    for tok in spec.getString.splitOn " " do
      let [a, b, c, k] := tok.splitOn "." |
        throwError "poly_def: bad monomial {tok}"
      let some a := a.toNat? | throwError "poly_def: bad exponent in {tok}"
      let some b := b.toNat? | throwError "poly_def: bad exponent in {tok}"
      let some c := c.toNat? | throwError "poly_def: bad exponent in {tok}"
      let some k := k.toInt? | throwError "poly_def: bad coefficient in {tok}"
      let kAbs := k.natAbs
      let mut factors : Array Expr := #[]
      if kAbs != 1 then
        let kE ← match numCache[kAbs]? with
          | some e => pure e
          | none => do
            let e ← mkNum kAbs
            numCache := numCache.insert kAbs e
            pure e
        factors := factors.push kE
      for (v, e) in [(xArr[0]!, a), (xArr[1]!, b), (xArr[2]!, c)] do
        if e == 1 then factors := factors.push v
        else if e > 1 then factors := factors.push (mkPowE v e)
      let term ←
        if factors.isEmpty then mkNum kAbs
        else pure (factors[1:].foldl mkMulE factors[0]!)
      acc := some <| match acc with
        | none => if k < 0 then mkNegE term else term
        | some e => if k < 0 then mkSubE e term else mkAddE e term
    let some body := acc | throwError "poly_def: empty polynomial"
    let body ← instantiateMVars body
    addDecl <| .defnDecl {
      name := name.getId, levelParams := [], type := mvp, value := body,
      hints := .abbrev, safety := .safe }
    if let some doc := doc then
      addDocStringCore name.getId doc.getDocString

/--
`poly_cert` closes goals `lhs = rhs` in `MvPolynomial (Fin 3) ℚ` where both
sides are built from `X 0`/`X 1`/`X 2`, numerals, `+`, `-`, `*`, `^`
(use it after `unfold`ing the certificate definitions).  The proof is checked
by one kernel evaluation of a sparse-polynomial normal-form comparison; no
`native_decide`, no new axioms.
-/
elab "poly_cert" : tactic => do
  liftMetaTactic fun g => do
    g.checkNotAssigned `poly_cert
    let ty ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := ty.consumeMData.eq?
      | throwError "poly_cert: goal is not an equality"
    let m₁ ← reify lhs
    let m₂ ← reify rhs
    -- Native predictor: fail fast and informatively before the kernel runs.
    match m₁.evalMap, m₂.evalMap with
    | none, _ | _, none =>
      throwError "poly_cert: monomial degree exceeds the digit bound 4096"
    | some d₁, some d₂ =>
      let d₁ := dropZeros d₁
      let d₂ := dropZeros d₂
      unless d₁.size == d₂.size &&
          d₁.fold (fun b k c => b && d₂.getD k 0 == c) true do
        let diffs := d₁.fold (fun a k c => if d₂.getD k 0 != c then a.push k else a) #[]
        let diffs := d₂.fold (fun a k c => if d₁.getD k 0 != c then a.push k else a) diffs
        throwError "poly_cert: sides differ on {diffs.size} monomial keys \
          (e.g. {diffs[0]?}); LHS has {d₁.size} monomials, RHS {d₂.size}"
    let e₁ := m₁.toPExprE
    let e₂ := m₂.toPExprE
    let rflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    g.assign <| mkApp3 (mkConst ``PolyCert.denote_eq_of_checkEq) e₁ e₂ rflTrue
    return []

end

end PolyCert

end ExplicitUnirational
