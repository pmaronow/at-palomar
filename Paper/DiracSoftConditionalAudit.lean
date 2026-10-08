module

public import Paper.DiracSoftConditional

@[expose] public section

/-! Reject nonstandard axioms in the actual pre-interface conditional displays. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``Paper.condExp_canonicalDiracState_before,
    ``Paper.condExp_selectedParisiDirac_gradient_before,
    ``Paper.condVar_canonicalDirac_tanh_before,
    ``Paper.condVar_selectedParisiDirac_tanh_before,
    ``Paper.selectedParisiDirac_variance_decomposition] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms Paper.condExp_selectedParisiDirac_gradient_before
#print axioms Paper.condVar_selectedParisiDirac_tanh_before
#print axioms Paper.selectedParisiDirac_variance_decomposition
