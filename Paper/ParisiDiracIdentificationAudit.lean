module

public import Paper.ParisiDiracIdentification

@[expose] public section

/-! Reject custom axioms and placeholders in the complete actual Dirac
PDE/state identification and its actual general variational observable. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``Paper.parisiPotential_dirac_eq_explicit,
    ``Paper.parisiGradient_dirac_eq_explicit,
    ``Paper.parisiHessian_dirac_hard,
    ``Paper.selectedParisiState_dirac_eq,
    ``Paper.hasLaw_selectedParisiState_dirac_interface,
    ``Paper.selectedParisiG_dirac_eq,
    ``Paper.selectedParisiG_dirac_minimum,
    ``Paper.parisiPDEFunctional_dirac_eq_rsFreeEnergy] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms Paper.parisiPotential_dirac_eq_explicit
#print axioms Paper.selectedParisiState_dirac_eq
#print axioms Paper.selectedParisiG_dirac_minimum

