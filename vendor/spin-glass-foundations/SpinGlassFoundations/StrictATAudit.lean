module

public import Lemmas.Gaussian.ConcreteModel

@[expose] public section

/-! Transitive kernel axiom audit for actual strict-AT bounds and fixed-point uniqueness. -/
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``SpinGlass.AT.quantitative_strictAT_on_compact,
    ``quantitative_strictAT,
    ``SpinGlass.AT.eq_rsQ_of_isRSFixedPoint,
    ``SpinGlass.AT.rsQ_fixedPoint_of_pos_field,
    ``PhysLean.Probability.GaussianIBP.IsGaussianHilbert.of_hasGaussianLaw] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"
#print axioms SpinGlass.AT.quantitative_strictAT_on_compact
#print axioms quantitative_strictAT
#print axioms SpinGlass.AT.eq_rsQ_of_isRSFixedPoint
#print axioms PhysLean.Probability.GaussianIBP.IsGaussianHilbert.of_hasGaussianLaw
