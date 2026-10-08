module

public import Paper.BoundedHeatGradientContinuity

@[expose] public section

/-! A rejecting transitive kernel audit of the actual bounded-measurable
source regularity used in full weak Parisi solution uniqueness. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``Paper.continuousAt_heatSemigroup_of_bounded,
    ``Paper.continuousAt_heatGradient_of_bounded,
    ``Paper.continuous_boundedVolterraPotential,
    ``Paper.hasDerivAt_boundedVolterraPotential_spatial,
    ``Paper.continuousOn_boundedVolterraGradient,
    ``Paper.norm_boundedVolterraGradient_sub_regularized_le] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms Paper.continuous_boundedVolterraPotential
#print axioms Paper.hasDerivAt_boundedVolterraPotential_spatial
#print axioms Paper.continuousOn_boundedVolterraGradient

