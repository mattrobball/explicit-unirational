module
public import ExplicitUnirational.WeightedProjective.Basic
open ExplicitUnirational ExplicitUnirational.WeightedProjectiveSpace MvPolynomial
#check (algebraMap ℚ (delPezzoGraded ℚ 0) : ℚ →+* delPezzoGraded ℚ 0)
#check (algebraMap (delPezzoGraded ℚ 0) (StandardChartRing ℚ 0))
#check (HomogeneousLocalization.Away.mk (delPezzoGraded ℚ) (mem_delPezzoGraded_X ℚ 0) 1 (X 1 : MvPolynomial (Fin 4) ℚ))
