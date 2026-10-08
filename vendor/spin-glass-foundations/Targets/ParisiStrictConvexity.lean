module

public import Targets.Section4Variance
public import Targets.Section5LambdaUPrime
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

@[expose] public section

/-!
# Strict convexity of the actual scalar Gaussian recursions

Talagrand's paired/scalar equality arguments require strict convexity, not
only the previously checked nonnegative Hessian. Positive input curvature
survives each genuine Gaussian smoothing, including mass and variance zero.
The arbitrary mass order is needed before sorting the scalar steps in §5.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- Positive input curvature gives a strictly positive averaged Hessian;
the additional tilted-variance contribution is nonnegative. -/
theorem stepD2_pos {A A' A'' : ℝ → ℝ} {m v : ℝ}
    (hm : 0 ≤ m) (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hAm : Measurable A) (hA'm : Measurable A') (hA''m : Measurable A'')
    (hpos : ∀ y, 0 < A'' y) (x : ℝ) :
    0 < stepD2 A A' A'' m v x := by
  have hE : 0 < tiltE A m v x := tiltE_pos hA hAm x
  have hQ : 0 < tiltQ A A'' m v x := by
    apply (integral_pos_iff_support_of_nonneg
      (fun z => (mul_pos (hpos _) (Real.exp_pos _)).le)
      (integrable_tiltQ hC2.abs_second_le_one hA hAm hA''m x)).mpr
    have hs : Function.support (fun z => A'' (x + Real.sqrt v * z) *
        Real.exp (m * A (x + Real.sqrt v * z))) = Set.univ := by
      ext z
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (mul_pos (hpos _) (Real.exp_pos _)).ne'
    rw [hs]
    simp
  have hCS : tiltP A A' m v x ^ 2 ≤ tiltR A A' m v x * tiltE A m v x :=
    sq_integral_mul_le hC2.abs_first_le_one hA hAm hA'm x
  have hvar : 0 ≤ tiltR A A' m v x / tiltE A m v x -
      (tiltP A A' m v x / tiltE A m v x) ^ 2 := by
    rw [sub_nonneg, div_pow, div_le_div_iff₀ (by positivity) hE]
    nlinarith [hCS, hE.le]
  exact add_pos_of_pos_of_nonneg (div_pos hQ hE) (mul_nonneg hm hvar)

/-- A strictly positive actual Hessian yields strict convexity on the line. -/
theorem strictConvexOn_of_hasParisiC2_pos {A A' A'' : ℝ → ℝ}
    (hC2 : HasParisiC2 A A' A'') (hpos : ∀ x, 0 < A'' x) :
    StrictConvexOn ℝ Set.univ A := by
  apply strictConvexOn_of_deriv2_pos convex_univ
    (continuous_iff_continuousAt.mpr (fun x => (hC2.1 x).continuousAt)).continuousOn
  intro x _
  have hd : deriv A = A' := funext fun y => (hC2.1 y).deriv
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, hd,
    (hC2.2.1 x).deriv] using hpos x

/-- Strict positivity at the log-cosh terminal. -/
theorem log_cosh_second_pos (x : ℝ) : 0 < 1 - (Real.sinh x / Real.cosh x) ^ 2 := by
  have hc := Real.cosh_pos x
  have hi := Real.cosh_sq_sub_sinh_sq x
  rw [sub_pos, div_pow, div_lt_one (sq_pos_of_pos hc)]
  linarith

/-- Every actual Parisi level has positive spatial curvature. -/
theorem parisiFSecond_pos {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) (x : ℝ) :
    0 < parisiFSecond s β j x := by
  induction j generalizing x with
  | zero => exact log_cosh_second_pos x
  | succ j ih =>
    exact stepD2_pos (s.m_nonneg (by omega)) (parisiF_hasLinearGrowth s β j)
      (parisiF_C2_props s β j).1 (parisiF_measurable s β j)
      (parisiF_C2_props s β j).2.1 (parisiF_C2_props s β j).2.2 ih x

theorem strictConvexOn_parisiF {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    StrictConvexOn ℝ Set.univ (parisiF s β j) :=
  strictConvexOn_of_hasParisiC2_pos (parisiF_C2_props s β j).1 (parisiFSecond_pos s β j)

theorem strictMono_parisiFDeriv {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    StrictMono (parisiFDeriv s β j) :=
  strictMono_of_hasDerivAt_pos (parisiF_C2_props s β j).1.2.1 (parisiFSecond_pos s β j)

/-- The scalar Hessian recursion with an arbitrary (possibly unsorted) mass list. -/
noncomputable def scalarFieldCascadeSecond (m v : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => 1 - (Real.sinh x / Real.cosh x) ^ 2
  | j + 1 => stepD2 (scalarFieldCascade m v j) (scalarFieldCascadeSlope m v j)
      (scalarFieldCascadeSecond m v j) (m j) (v j)

/-- Second-order regularity and positive curvature hold before scalar mass sorting. -/
theorem scalarFieldCascade_C2_pos (m v : ℕ → ℝ) (hm : ∀ j, m j ∈ Set.Icc 0 1)
    (j : ℕ) :
    HasParisiC2 (scalarFieldCascade m v j) (scalarFieldCascadeSlope m v j)
      (scalarFieldCascadeSecond m v j) ∧
    Measurable (scalarFieldCascadeSlope m v j) ∧
    Measurable (scalarFieldCascadeSecond m v j) ∧
    ∀ x, 0 < scalarFieldCascadeSecond m v j x := by
  induction j with
  | zero =>
    refine ⟨hasParisiC2_log_cosh, ?_, ?_, log_cosh_second_pos⟩
    · exact Real.measurable_sinh.div Real.measurable_cosh
    · exact measurable_const.sub ((Real.measurable_sinh.div Real.measurable_cosh).pow_const 2)
  | succ j ih =>
    have hp := scalarFieldCascade_props m v j
    exact ⟨hasParisiC2_parisiStep_nonneg (hm j).1 (hm j).2 ih.1 hp.2.1 hp.1
      ih.2.1 ih.2.2.1, measurable_stepD1 hp.1 ih.2.1 _ _,
      measurable_stepD2 hp.1 ih.2.1 ih.2.2.1 _ _,
      stepD2_pos (hm j).1 hp.2.1 ih.1 hp.1 ih.2.1 ih.2.2.1 ih.2.2.2⟩

theorem strictConvexOn_scalarFieldCascade (m v : ℕ → ℝ)
    (hm : ∀ j, m j ∈ Set.Icc 0 1) (j : ℕ) :
    StrictConvexOn ℝ Set.univ (scalarFieldCascade m v j) :=
  strictConvexOn_of_hasParisiC2_pos (scalarFieldCascade_C2_pos m v hm j).1
    (scalarFieldCascade_C2_pos m v hm j).2.2.2

theorem strictMono_scalarFieldCascadeSlope (m v : ℕ → ℝ)
    (hm : ∀ j, m j ∈ Set.Icc 0 1) (j : ℕ) :
    StrictMono (scalarFieldCascadeSlope m v j) :=
  strictMono_of_hasDerivAt_pos (scalarFieldCascade_C2_pos m v hm j).1.2.1
    (scalarFieldCascade_C2_pos m v hm j).2.2.2

/-- Centered Gaussian smoothing preserves evenness, including mass zero. -/
theorem parisiStep_even {A : ℝ → ℝ} (hA : Function.Even A) (m v : ℝ) :
    Function.Even (parisiStep m v A) := by
  have hp : MeasurePreserving (fun z : ℝ => -z) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_neg, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩
  intro x
  have H (f : ℝ → ℝ) :
      (∫ z, f (A (-x + Real.sqrt v * z)) ∂gaussianReal 0 1) =
        ∫ z, f (A (x + Real.sqrt v * z)) ∂gaussianReal 0 1 := by
    have he (z : ℝ) : A (-x + Real.sqrt v * z) = A (x + Real.sqrt v * (-z)) := by
      rw [show -x + Real.sqrt v * z = -(x + Real.sqrt v * (-z)) by ring, hA]
    simp_rw [he]
    exact hp.integral_comp measurableEmbedding_neg (fun z : ℝ => f (A (x + Real.sqrt v * z)))
  unfold parisiStep
  split_ifs
  · exact H id
  · rw [H (fun z => Real.exp (m * z))]

theorem scalarFieldCascade_even (m v : ℕ → ℝ) (j : ℕ) :
    Function.Even (scalarFieldCascade m v j) := by
  induction j with
  | zero => intro x; simp [scalarFieldCascade, Real.cosh_neg]
  | succ j ih => exact parisiStep_even ih _ _

theorem parisiF_even {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    Function.Even (parisiF s β j) := by
  induction j with
  | zero => intro x; simp [parisiF, Real.cosh_neg]
  | succ j ih => exact parisiStep_even ih _ _

/-- Equal translated profiles up to an additive constant force equal shifts
when the actual spatial slope is strictly increasing. -/
theorem eq_of_sub_translate_eq_const_of_strictMono_deriv {A A' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt A (A' x) x) (hmono : StrictMono A')
    {x y c : ℝ} (he : ∀ z, A (x + z) - A (y + z) = c) : x = y := by
  have H := ((hd (x + 0)).comp 0 ((hasDerivAt_id 0).const_add x)).sub
    ((hd (y + 0)).comp 0 ((hasDerivAt_id 0).const_add y))
  have heq : (fun z => A (x + z) - A (y + z)) = fun _ => c := funext he
  change HasDerivAt (fun z => A (x + z) - A (y + z))
    (A' (x + 0) * 1 - A' (y + 0) * 1) 0 at H
  rw [heq] at H
  have hh := H.unique (hasDerivAt_const 0 c)
  simp only [add_zero, mul_one] at hh
  exact hmono.injective (sub_eq_zero.mp hh)

end SpinGlass.Targets
