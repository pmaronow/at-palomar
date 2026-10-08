module

public import Paper.HJBGridCells

@[expose] public section

/-! Reject unexpected transitive axioms in the exact finite-grid HJB bridge. -/
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``Paper.hjbGrid_cell_potential,
    ``Paper.hjbGrid_cell_gradient,
    ``Paper.hjbGrid_cell_error_integral,
    ``Paper.hjbGrid_cell_control_error_bounds] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms Paper.hjbGrid_cell_control_error_bounds

