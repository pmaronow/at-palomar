module

public import Paper.NumberedResults

@[expose] public section

/-! Typed one-to-one statements for all fifteen numbered results, followed by
a rejecting transitive axiom audit. No additional mathematical premise is
supplied to any numbered proof. -/

example : Paper.Numbered.Statement_1_1 := Paper.Numbered.result_1_1
example : Paper.Numbered.Statement_1_2 := Paper.Numbered.result_1_2
example : Paper.Numbered.Statement_2_1 := Paper.Numbered.result_2_1
example : Paper.Numbered.Statement_2_2 := Paper.Numbered.result_2_2
example : Paper.Numbered.Statement_2_3 := Paper.Numbered.result_2_3
example : Paper.Numbered.Statement_3_1 := Paper.Numbered.result_3_1
example : Paper.Numbered.Statement_4_1 := Paper.Numbered.result_4_1
example : Paper.Numbered.Statement_5_1 := Paper.Numbered.result_5_1
example : Paper.Numbered.Statement_5_2 := Paper.Numbered.result_5_2
example : Paper.Numbered.Statement_5_3 := Paper.Numbered.result_5_3
example : Paper.Numbered.Statement_5_4 := Paper.Numbered.result_5_4
example : Paper.Numbered.Statement_5_5 := Paper.Numbered.result_5_5
example : Paper.Numbered.Statement_5_6 := Paper.Numbered.result_5_6
example : Paper.Numbered.Statement_6_1 := Paper.Numbered.result_6_1
example : Paper.Numbered.Statement_6_2 := Paper.Numbered.result_6_2

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``Paper.Numbered.result_1_1,
    ``Paper.Numbered.result_1_2,
    ``Paper.Numbered.result_2_1,
    ``Paper.Numbered.result_2_2,
    ``Paper.Numbered.result_2_3,
    ``Paper.Numbered.result_3_1,
    ``Paper.Numbered.result_4_1,
    ``Paper.Numbered.result_5_1,
    ``Paper.Numbered.result_5_2,
    ``Paper.Numbered.result_5_3,
    ``Paper.Numbered.result_5_4,
    ``Paper.Numbered.result_5_5,
    ``Paper.Numbered.result_5_6,
    ``Paper.Numbered.result_6_1,
    ``Paper.Numbered.result_6_2] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms Paper.Numbered.result_1_1
#print axioms Paper.Numbered.result_1_2
#print axioms Paper.Numbered.result_2_1
#print axioms Paper.Numbered.result_2_2
#print axioms Paper.Numbered.result_2_3
#print axioms Paper.Numbered.result_3_1
#print axioms Paper.Numbered.result_4_1
#print axioms Paper.Numbered.result_5_1
#print axioms Paper.Numbered.result_5_2
#print axioms Paper.Numbered.result_5_3
#print axioms Paper.Numbered.result_5_4
#print axioms Paper.Numbered.result_5_5
#print axioms Paper.Numbered.result_5_6
#print axioms Paper.Numbered.result_6_1
#print axioms Paper.Numbered.result_6_2
