module

public import Targets.ParisiMassLocal

@[expose] public section

/-!
# Joint mass, variance, and field continuity on actual Parisi inputs

The spatial derivative is a quotient of continuous Gaussian exponential
integrals, whose denominator stays positive at mass zero. For the scalar
transform itself, the existing uniform Herbst bound connects the actual
zero-mass branch to the nonzero branch, including zero variance.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- Joint continuity of the Gaussian exponential moment with a bounded
continuous observable. Local domination uses only linear growth of the input. -/
theorem continuous_gaussian_weighted_exp_joint {A G : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hcA : Continuous A) (hcG : Continuous G)
    (hG : ∀ x, |G x| ≤ 1) :
    Continuous (fun q : ℝ × (ℝ × ℝ) => ∫ z,
      G (q.2.2 + Real.sqrt q.2.1 * z) *
        Real.exp (q.1 * A (q.2.2 + Real.sqrt q.2.1 * z)) ∂(gaussianReal 0 1)) := by
  obtain ⟨C, D, hC, hD, hb⟩ := hA
  apply continuous_iff_continuousAt.mpr
  intro q
  let M := |q.1| + 1
  let X := |q.2.2| + 1
  let V := |q.2.1| + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hevent : ∀ᶠ p : ℝ × (ℝ × ℝ) in 𝓝 q,
      |p.1| ≤ M ∧ |p.2.2| ≤ X ∧ p.2.1 ≤ V := by
    have hm : ∀ᶠ p : ℝ × (ℝ × ℝ) in 𝓝 q, |p.1| < M :=
      (continuous_fst.abs.continuousAt).eventually (Iio_mem_nhds (by dsimp [M]; linarith))
    have hx : ∀ᶠ p : ℝ × (ℝ × ℝ) in 𝓝 q, |p.2.2| < X :=
      (continuous_snd.snd.abs.continuousAt).eventually (Iio_mem_nhds (by dsimp [X]; linarith))
    have hv : ∀ᶠ p : ℝ × (ℝ × ℝ) in 𝓝 q, p.2.1 < V :=
      (continuous_snd.fst.continuousAt).eventually
        (Iio_mem_nhds (by dsimp [V]; linarith [le_abs_self q.2.1]))
    filter_upwards [hm, hx, hv] with p hpM hpX hpV
    exact ⟨hpM.le, hpX.le, hpV.le⟩
  apply continuousAt_of_dominated
    (bound := fun z : ℝ => Real.exp (M * (C + D * X)) * Real.exp ((M * D * Real.sqrt V) * |z|))
  · filter_upwards with p
    exact ((hcG.measurable.comp (measurable_tilt_shift _ _)).mul
      ((hcA.measurable.comp (measurable_tilt_shift _ _)).const_mul p.1).exp).aestronglyMeasurable
  · filter_upwards [hevent] with p hp
    filter_upwards with z
    have hshift : |p.2.2 + Real.sqrt p.2.1 * z| ≤ X + Real.sqrt V * |z| := by
      have H := abs_add_le p.2.2 (Real.sqrt p.2.1 * z)
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at H
      nlinarith [mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hp.2.2) (abs_nonneg z), hp.2.1]
    have hinput : |A (p.2.2 + Real.sqrt p.2.1 * z)| ≤ C + D * X + D * Real.sqrt V * |z| := by
      nlinarith [hb (p.2.2 + Real.sqrt p.2.1 * z), mul_le_mul_of_nonneg_left hshift hD]
    have hprod := mul_le_mul hp.1 hinput (abs_nonneg _) hM
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (p.1 * A (p.2.2 + Real.sqrt p.2.1 * z)) := by
        simpa using mul_le_mul_of_nonneg_right (hG _) (Real.exp_pos _).le
      _ ≤ _ := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have H := le_abs_self (p.1 * A (p.2.2 + Real.sqrt p.2.1 * z))
        rw [abs_mul] at H
        nlinarith
  · exact (integrable_exp_abs_mul_stdGaussian (M * D * Real.sqrt V)).const_mul _
  · filter_upwards with z
    have hshift : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.2 + Real.sqrt p.2.1 * z) := by fun_prop
    exact ((hcG.comp hshift).mul
      (Real.continuous_exp.comp (continuous_fst.mul (hcA.comp hshift)))).continuousAt

/-- The normalizing moment is jointly continuous, including zero mass and
zero variance. Its positivity is supplied by the existing linear-growth API. -/
theorem continuous_tiltE_mass_variance_spatial {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hcA : Continuous A) :
    Continuous (fun q : ℝ × (ℝ × ℝ) => tiltE A q.1 q.2.1 q.2.2) := by
  simpa only [tiltE, one_mul] using
    continuous_gaussian_weighted_exp_joint hA hcA (G := fun _ => 1) continuous_const (by simp)

/-- The actual first spatial derivative has no singular mass-zero branch:
the same normalized exponential quotient is jointly continuous everywhere. -/
theorem continuous_stepD1_mass_variance_spatial {A A' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hcA : Continuous A) (hcA' : Continuous A')
    (hA' : ∀ x, |A' x| ≤ 1) :
    Continuous (fun q : ℝ × (ℝ × ℝ) => stepD1 A A' q.1 q.2.1 q.2.2) := by
  exact (continuous_gaussian_weighted_exp_joint hA hcA hcA' hA').div
    (continuous_tiltE_mass_variance_spatial hA hcA)
    (fun q => (tiltE_pos hA hcA.measurable q.2.2).ne')

/-- Joint continuity of the actual scalar step on the full admissible
mass/variance domain, with both the mass-zero and variance-zero faces included. -/
theorem continuousOn_parisiStep_parisiF_joint {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => parisiStep p.1 p.2.1 (parisiF s β j) p.2.2)
      (Set.Icc 0 1 ×ˢ Set.Ici 0 ×ˢ Set.univ) := by
  let A := parisiF s β j
  have hA := parisiF_hasLinearGrowth s β j
  have hAm := parisiF_measurable s β j
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun x =>
    ((parisiF_C2_props s β j).1.1 x).continuousAt
  have hcI := continuous_tiltE_mass_variance_spatial hA hcA
  have hc0 : Continuous (fun p : ℝ × (ℝ × ℝ) => parisiStep 0 p.2.1 A p.2.2) :=
    ((continuous_parisiStep_variance_spatial (parisiF_C2_props s β j).1
      (continuous_parisiFSecond s β j) (m := 0) le_rfl).1).comp continuous_snd
  intro p hp
  by_cases hm : p.1 = 0
  · have hgap : ∀ᶠ q : ℝ × (ℝ × ℝ) in 𝓝[Set.Icc 0 1 ×ˢ Set.Ici 0 ×ˢ Set.univ] p,
        |parisiStep q.1 q.2.1 A q.2.2 - parisiStep 0 q.2.1 A q.2.2| ≤ |q.1| * q.2.1 / 2 := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      simpa only [mul_div_assoc] using
        abs_parisiStep_mass_sub_zero_le hA hAm (parisiF_lipschitz s β j) hq.2.1 q.1 q.2.2
    have hlim : Tendsto (fun q : ℝ × (ℝ × ℝ) => |q.1| * q.2.1 / 2)
        (𝓝[Set.Icc 0 1 ×ˢ Set.Ici 0 ×ˢ Set.univ] p) (𝓝 0) := by
      have H := ((continuous_fst.abs.mul continuous_snd.fst).div_const 2).continuousWithinAt (s := Set.Icc 0 1 ×ˢ Set.Ici 0 ×ˢ Set.univ) (x := p)
      simpa only [Pi.mul_apply, hm, abs_zero, zero_mul, zero_div] using H.tendsto
    have hd : Tendsto (fun q : ℝ × (ℝ × ℝ) =>
        parisiStep q.1 q.2.1 A q.2.2 - parisiStep 0 q.2.1 A q.2.2)
        (𝓝[Set.Icc 0 1 ×ˢ Set.Ici 0 ×ˢ Set.univ] p) (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hgap hlim
    have H := hd.add hc0.continuousWithinAt.tendsto
    rw [ContinuousWithinAt, hm]
    simpa only [sub_add_cancel, zero_add, A] using H
  · have H : ContinuousAt (fun q : ℝ × (ℝ × ℝ) =>
        (1 / q.1) * Real.log (tiltE A q.1 q.2.1 q.2.2)) p :=
      (continuousAt_const.div continuous_fst.continuousAt hm).mul
        (hcI.continuousAt.log (tiltE_pos hA hAm p.2.2).ne')
    apply H.continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [(continuous_fst.continuousWithinAt (s := Set.Icc 0 1 ×ˢ Set.Ici 0 ×ˢ Set.univ) (x := p)).eventually_ne hm] with q hq
      simp only [parisiStep, if_neg hq, tiltE, A]
    · simp only [parisiStep, if_neg hm, tiltE, A]

/-- Joint continuity of the actual spatial derivative on the same closed
mass/variance domain used by the Section 4 normalized squared-slope factor. -/
theorem continuousOn_stepD1_parisiF_joint {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      stepD1 (parisiF s β j) (parisiFDeriv s β j) p.1 p.2.1 p.2.2)
      (Set.Icc 0 1 ×ˢ Set.Ici 0 ×ˢ Set.univ) := by
  have hcA : Continuous (parisiF s β j) := continuous_iff_continuousAt.mpr fun x =>
    ((parisiF_C2_props s β j).1.1 x).continuousAt
  have hcA' : Continuous (parisiFDeriv s β j) := continuous_iff_continuousAt.mpr fun x =>
    ((parisiF_C2_props s β j).1.2.1 x).continuousAt
  exact (continuous_stepD1_mass_variance_spatial (parisiF_hasLinearGrowth s β j)
    hcA hcA' (parisiF_C2_props s β j).1.abs_first_le_one).continuousOn

end SpinGlass.Targets
