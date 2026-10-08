module

public import Targets.TalagrandFinal
public import Lemmas.Gaussian.ConcreteModel

@[expose] public section

/-! Kernel axiom audit for the vendored foundational results.
The only allowed axioms are Lean's usual extensionality, choice and quotient axioms.
This command fails compilation if a placeholder, native decision oracle or custom axiom
occurs anywhere in a critical theorem's transitive dependency graph. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``SpinGlass.Targets.parisi_formula,
    ``SpinGlass.Targets.talagrand_theorem_2_2,
    ``SpinGlass.AT.quantitative_strictAT_on_compact,
    ``quantitative_strictAT,
    ``SpinGlass.AT.eq_rsQ_of_isRSFixedPoint,
    ``SpinGlass.AT.rsQ_fixedPoint_of_pos_field] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms SpinGlass.Targets.parisi_formula
#print axioms SpinGlass.AT.quantitative_strictAT_on_compact
#print axioms quantitative_strictAT
#print axioms SpinGlass.AT.eq_rsQ_of_isRSFixedPoint
