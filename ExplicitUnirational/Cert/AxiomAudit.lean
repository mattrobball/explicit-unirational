/-
Copyright (c) 2026 Matthew R. Ballard.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew R. Ballard
-/
module

public import ExplicitUnirational.Cert.Invariants
public import ExplicitUnirational.Cert.NonicF5
public import ExplicitUnirational.Cert.OcticF7
public import ExplicitUnirational.Cert.SexticF5

/-!
# Axiom audit for the Appendix A certificates

Each of the three irreducibility claims of note Appendix A must depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Anything else -- in particular `sorryAx` -- is a defect.
-/

#print axioms ExplicitUnirational.Rabin.irreducible_of_rabin
#print axioms ExplicitUnirational.Cert.irreducible_f8
#print axioms ExplicitUnirational.Cert.irreducible_R
#print axioms ExplicitUnirational.Cert.irreducible_d6
#print axioms ExplicitUnirational.Invariants.hessian_identity_rat
#print axioms ExplicitUnirational.Invariants.c4_c6_rat
#print axioms ExplicitUnirational.Invariants.c4_c6_lambda
#print axioms ExplicitUnirational.Invariants.hessian_lambda
