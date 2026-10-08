module

public import Paper.RSFunctional
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Tactic

@[expose] public section

/-!
# Measurable-time integral Picard construction

Unlike the classical continuous-time ODE theorem, the integral equation here
allows jumps of a probability distribution's CDF. A bounded measurable drift
which is globally Lipschitz in space has a unique continuous pathwise solution
on each finite horizon. The construction uses a contracting iterate of Picard's
integral map, with the actual factorial bound.
-/

noncomputable section
open Function intervalIntegral MeasureTheory Metric Set Filter
open scoped Nat NNReal Topology
namespace Paper

/-- The assumptions needed for an integral equation, allowing discontinuous time dependence. -/
structure IsBoundedMeasurableDrift (f : ℝ → ℝ → ℝ) (L K : ℝ≥0) : Prop where
  measurable : Measurable (Function.uncurry f)
  norm_le : ∀ t x, ‖f t x‖ ≤ L
  lipschitz : ∀ t, LipschitzWith K (f t)

namespace IntegralPicard
variable {T : ℝ} (hT : 0 ≤ T) (h : ℝ) (L : ℝ≥0)
def zeroTime : Icc (0 : ℝ) T := ⟨0, ⟨le_rfl, hT⟩⟩
abbrev Curve := ODE.FunSpace (zeroTime hT) h 0 L
variable {h L} {K : ℝ≥0} {f : ℝ → ℝ → ℝ}

lemma integrable_comp (hf : IsBoundedMeasurableDrift f L K) (α : Curve hT h L)
    (t : Icc (0 : ℝ) T) :
    IntervalIntegrable (fun s => f s (α.compProj s)) volume 0 t := by
  apply (intervalIntegrable_const (c := (L : ℝ))).mono_fun'
    (hf.measurable.comp (measurable_id.prodMk α.continuous_compProj.measurable)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s => hf.norm_le s (α.compProj s))

/-- Picard's integral map on the complete space of bounded-slope curves. -/
def next (hf : IsBoundedMeasurableDrift f L K) (α : Curve hT h L) : Curve hT h L where
  toFun t := h + ∫ s in 0..t.1, f s (α.compProj s)
  lipschitzWith := LipschitzWith.of_dist_le_mul fun t₁ t₂ => by
    rw [dist_eq_norm, add_sub_add_left_eq_sub,
      integral_interval_sub_left (integrable_comp hT hf α t₁) (integrable_comp hT hf α t₂),
      Subtype.dist_eq, Real.dist_eq]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    exact hf.norm_le s _
  mem_closedBall₀ := by simp [zeroTime]

@[simp] lemma next_apply (hf : IsBoundedMeasurableDrift f L K) (α : Curve hT h L)
    (t : Icc (0 : ℝ) T) : next hT hf α t = h + ∫ s in 0..t.1, f s (α.compProj s) := rfl

lemma dist_comp_iterate_le (hf : IsBoundedMeasurableDrift f L K)
    (n : ℕ) (t : Icc (0 : ℝ) T) {α γ : Curve hT h L}
    (hh : dist ((next hT hf)^[n] α t) ((next hT hf)^[n] γ t) ≤
      (K * |t.1 - 0|) ^ n / n ! * dist α γ) :
    dist (f t ((next hT hf)^[n] α t)) (f t ((next hT hf)^[n] γ t)) ≤
      K ^ (n + 1) * |t.1 - 0| ^ n / n ! * dist α γ := by
  calc
    _ ≤ K * dist ((next hT hf)^[n] α t) ((next hT hf)^[n] γ t) :=
      (hf.lipschitz t).dist_le_mul _ _
    _ ≤ K ^ (n + 1) * |t.1 - 0| ^ n / n ! * dist α γ := by
      rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
      gcongr
      rwa [← mul_pow]

/-- The genuine factorial estimate for iterated integral Picard maps. -/
lemma dist_iterate_apply_le (hf : IsBoundedMeasurableDrift f L K)
    (α γ : Curve hT h L) (n : ℕ) (t : Icc (0 : ℝ) T) :
    dist ((next hT hf)^[n] α t) ((next hT hf)^[n] γ t) ≤
      (K * |t.1 - 0|) ^ n / n ! * dist α γ := by
  induction n generalizing t with
  | zero => simpa using!
      ContinuousMap.dist_apply_le_dist (f := ODE.FunSpace.toContinuousMap α) (g := ODE.FunSpace.toContinuousMap γ) t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply, next_apply,
      add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
        (integrable_comp hT hf _ t) (integrable_comp hT hf _ t)]
    calc
      _ ≤ ∫ s in uIoc (0 : ℝ) t.1, K ^ (n + 1) * |s - 0| ^ n / n ! * dist α γ := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro s hs
        have hs' : s ∈ Icc (0 : ℝ) T :=
          subset_trans uIoc_subset_uIcc (uIcc_subset_Icc ⟨le_rfl, hT⟩ t.2) hs
        rw [← dist_eq_norm, ODE.FunSpace.compProj_of_mem, ODE.FunSpace.compProj_of_mem]
        exact dist_comp_iterate_le hT hf n ⟨s, hs'⟩ (hn _)
      _ ≤ (K * |t.1 - 0|) ^ (n + 1) / (n + 1) ! * dist α γ := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div,
          Nat.abs_cast, ← Nat.cast_succ]
        simp only [Nat.abs_cast]
        rw [← Nat.cast_mul, ← Nat.factorial_succ, ← mul_pow]

lemma dist_iterate_le (hf : IsBoundedMeasurableDrift f L K)
    (α γ : Curve hT h L) (n : ℕ) :
    dist ((next hT hf)^[n] α) ((next hT hf)^[n] γ) ≤
      (K * T) ^ n / n ! * dist α γ := by
  rw [← MetricSpace.isometry_induced ODE.FunSpace.toContinuousMap
    ODE.FunSpace.toContinuousMap.injective |>.dist_eq, ContinuousMap.dist_le]
  · intro t
    apply le_trans (dist_iterate_apply_le hT hf α γ n t)
    gcongr
    simpa only [sub_zero, abs_of_nonneg t.2.1] using t.2.2
  · positivity

lemma exists_contracting_iterate (hf : IsBoundedMeasurableDrift f L K) :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C (next (h := h) hT hf)^[n] := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * T)
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hC : 0 ≤ ((K : ℝ) * T) ^ n / n ! := by positivity
  exact ⟨n, ⟨_, hC⟩, hn, LipschitzWith.of_dist_le_mul fun α γ => dist_iterate_le hT hf α γ n⟩

/-- A bounded measurable spatially Lipschitz drift has an actual integral solution. -/
theorem exists_fixedPoint (hf : IsBoundedMeasurableDrift f L K) :
    ∃ α : Curve hT h L, IsFixedPt (next hT hf) α := by
  obtain ⟨n, C, hc⟩ := exists_contracting_iterate (h := h) hT hf
  exact ⟨_, hc.isFixedPt_fixedPoint_iterate⟩

/-- The integral solution is unique in the complete curve space. -/
theorem fixedPoint_unique (hf : IsBoundedMeasurableDrift f L K)
    {α γ : Curve hT h L} (ha : IsFixedPt (next hT hf) α) (hg : IsFixedPt (next hT hf) γ) :
    α = γ := by
  obtain ⟨n, C, hc⟩ := exists_contracting_iterate (h := h) hT hf
  exact hc.fixedPoint_unique' (ha.iterate n) (hg.iterate n)

/-- The chosen fixed point is an actual bounded-slope solution. -/
def solution (hf : IsBoundedMeasurableDrift f L K) : Curve hT h L :=
  Classical.choose (exists_fixedPoint (h := h) hT hf)

lemma solution_fixed (hf : IsBoundedMeasurableDrift f L K) :
    IsFixedPt (next hT hf) (solution (h := h) hT hf) :=
  Classical.choose_spec (exists_fixedPoint (h := h) hT hf)

lemma solution_equation (hf : IsBoundedMeasurableDrift f L K) (t : Icc (0 : ℝ) T) :
    solution (h := h) hT hf t = h + ∫ s in 0..t.1, f s ((solution (h := h) hT hf).compProj s) := by
  exact (congrArg (fun α : Curve hT h L => α t) (solution_fixed hT hf)).symm

/-- Every continuous solution of the integral equation equals the constructed one. -/
theorem real_solution_unique (hf : IsBoundedMeasurableDrift f L K)
    (Y : ℝ → ℝ) (hY : Continuous Y)
    (hYe : ∀ t ∈ Icc (0 : ℝ) T, Y t = h + ∫ s in 0..t, f s (Y s)) :
    ∀ t ∈ Icc (0 : ℝ) T, Y t = (solution (h := h) hT hf).compProj t := by
  have hYi (t : Icc (0 : ℝ) T) : IntervalIntegrable (fun s => f s (Y s)) volume 0 t := by
    apply (intervalIntegrable_const (c := (L : ℝ))).mono_fun'
      (hf.measurable.comp (measurable_id.prodMk hY.measurable)).aestronglyMeasurable
    exact Eventually.of_forall (fun s => hf.norm_le s (Y s))
  let α : Curve hT h L := {
    toFun := fun t => Y t
    lipschitzWith := LipschitzWith.of_dist_le_mul fun t₁ t₂ => by
      rw [hYe t₁ t₁.2, hYe t₂ t₂.2, dist_eq_norm, add_sub_add_left_eq_sub,
        integral_interval_sub_left (hYi t₁) (hYi t₂), Subtype.dist_eq, Real.dist_eq]
      exact intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => hf.norm_le s (Y s))
    mem_closedBall₀ := by simp [zeroTime, hYe 0 ⟨le_rfl, hT⟩] }
  have haf : IsFixedPt (next hT hf) α := by
    apply ODE.FunSpace.ext
    intro t
    change h + (∫ s in 0..t.1, f s (α.compProj s)) = Y t
    rw [hYe t t.2]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) T :=
      (uIcc_subset_Icc ⟨le_rfl, hT⟩ t.2) hs
    dsimp only
    rw [ODE.FunSpace.compProj_of_mem hs']
  have he : α = solution (h := h) hT hf := fixedPoint_unique hT hf haf (solution_fixed hT hf)
  intro t ht
  rw [ODE.FunSpace.compProj_of_mem ht]
  exact congrArg (fun γ : Curve hT h L => γ ⟨t, ht⟩) he

lemma next_dist_le (hf : IsBoundedMeasurableDrift f L K) (α γ : Curve hT h L) :
    dist (next hT hf α) (next hT hf γ) ≤ (K : ℝ) * T * dist α γ := by
  simpa only [Function.iterate_one, pow_one, Nat.factorial_one, Nat.cast_one, div_one] using
    dist_iterate_le hT hf α γ 1

/-- A uniform drift perturbation controls one integral Picard step. -/
lemma next_drift_dist_le {g : ℝ → ℝ → ℝ}
    (hf : IsBoundedMeasurableDrift f L K) (hg : IsBoundedMeasurableDrift g L K)
    (δ : ℝ) (hδ : 0 ≤ δ) (hfg : ∀ t x, dist (f t x) (g t x) ≤ δ)
    (α : Curve hT h L) : dist (next hT hf α) (next hT hg α) ≤ δ * T := by
  rw [← MetricSpace.isometry_induced ODE.FunSpace.toContinuousMap
    ODE.FunSpace.toContinuousMap.injective |>.dist_eq, ContinuousMap.dist_le]
  · intro t
    rw [ODE.FunSpace.toContinuousMap_apply_eq_apply, ODE.FunSpace.toContinuousMap_apply_eq_apply,
      dist_eq_norm, next_apply, next_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (integrable_comp hT hf α t) (integrable_comp hT hg α t)]
    have hb : ‖∫ s in (0 : ℝ)..t.1, f s (α.compProj s) - g s (α.compProj s)‖ ≤ δ * |t.1 - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => by
        simpa only [← dist_eq_norm] using hfg s (α.compProj s))
    exact hb.trans (mul_le_mul_of_nonneg_left (by simpa only [sub_zero, abs_of_nonneg t.2.1] using t.2.2) hδ)
  · positivity

/-- A finite sensitivity constant, avoiding any time differentiability assumption. -/
def sensitivity (K : ℝ≥0) (T : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (K : ℝ) * T * sensitivity K T n + T

lemma sensitivity_nonneg (hT : 0 ≤ T) (n : ℕ) : 0 ≤ sensitivity K T n := by
  induction n with
  | zero => rfl
  | succ n hn => exact add_nonneg (mul_nonneg (mul_nonneg K.2 hT) hn) hT

lemma iterate_drift_dist_le {g : ℝ → ℝ → ℝ}
    (hf : IsBoundedMeasurableDrift f L K) (hg : IsBoundedMeasurableDrift g L K)
    (δ : ℝ) (hδ : 0 ≤ δ) (hfg : ∀ t x, dist (f t x) (g t x) ≤ δ)
    (α : Curve hT h L) (n : ℕ) :
    dist ((next hT hf)^[n] α) ((next hT hg)^[n] α) ≤ sensitivity K T n * δ := by
  induction n with
  | zero => simp [sensitivity]
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply']
    calc
      _ ≤ dist (next hT hf ((next hT hf)^[n] α)) (next hT hf ((next hT hg)^[n] α)) +
          dist (next hT hf ((next hT hg)^[n] α)) (next hT hg ((next hT hg)^[n] α)) := dist_triangle _ _ _
      _ ≤ ((K : ℝ) * T) * (sensitivity K T n * δ) + δ * T :=
        add_le_add ((next_dist_le hT hf _ _).trans (mul_le_mul_of_nonneg_left hn (mul_nonneg K.2 hT)))
          (next_drift_dist_le hT hf hg δ hδ hfg _)
      _ = sensitivity K T (n + 1) * δ := by simp only [sensitivity]; ring

/-- Quantitative stability of the genuine integral solution under drift perturbation. -/
lemma solution_drift_dist_le {g : ℝ → ℝ → ℝ}
    (hf : IsBoundedMeasurableDrift f L K) (hg : IsBoundedMeasurableDrift g L K)
    (δ : ℝ) (hδ : 0 ≤ δ) (hfg : ∀ t x, dist (f t x) (g t x) ≤ δ)
    (n : ℕ) (hn : ((K : ℝ) * T) ^ n / n ! < 1) :
    dist (solution (h := h) hT hf) (solution (h := h) hT hg) ≤
      sensitivity K T n / (1 - ((K : ℝ) * T) ^ n / n !) * δ := by
  let α := solution (h := h) hT hf
  let γ := solution (h := h) hT hg
  have ha : (next hT hf)^[n] α = α := (solution_fixed hT hf).iterate n
  have hg' : (next hT hg)^[n] γ = γ := (solution_fixed hT hg).iterate n
  have hd : dist α γ ≤ ((K : ℝ) * T) ^ n / n ! * dist α γ + sensitivity K T n * δ := by
    nth_rw 1 [← ha, ← hg']
    exact (dist_triangle _ ((next hT hf)^[n] γ) _).trans
      (add_le_add (dist_iterate_le hT hf α γ n) (iterate_drift_dist_le hT hf hg δ hδ hfg γ n))
  have hpos : 0 < 1 - ((K : ℝ) * T) ^ n / n ! := sub_pos.mpr hn
  have hb : dist α γ ≤ (sensitivity K T n * δ) /
      (1 - ((K : ℝ) * T) ^ n / n !) := (le_div_iff₀ hpos).mpr (by nlinarith [hd])
  convert hb using 1 <;> ring

end IntegralPicard

/-- The nonnegative uniform drift bound and spatial Lipschitz constant. -/
def parisiDriftConstant (β : ℝ) : ℝ≥0 := ⟨β ^ 2, sq_nonneg β⟩

/-- The actual measurable-time drift after subtracting additive noise. -/
def parisiNoiseDrift (β : ℝ) (μ : ParisiMeasure) (v : ℝ → ℝ → ℝ)
    (W : ℝ → ℝ) (t y : ℝ) : ℝ :=
  β ^ 2 * parisiCDF μ t * v t (y + β * W t)

/-- CDF jumps preserve the measurable, bounded, spatially Lipschitz hypotheses. -/
theorem isBoundedMeasurableDrift_parisiNoiseDrift (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ → ℝ → ℝ) (hv : Continuous (Function.uncurry v))
    (hvbound : ∀ t x, ‖v t x‖ ≤ 1)
    (hvlip : ∀ t, LipschitzWith 1 (v t))
    (W : ℝ → ℝ) (hW : Continuous W) :
    IsBoundedMeasurableDrift (parisiNoiseDrift β μ v W)
      (parisiDriftConstant β) (parisiDriftConstant β) := by
  constructor
  · exact (((measurable_const.mul ((parisiCDF_monotone μ).measurable.comp measurable_fst))).mul
      (hv.measurable.comp (measurable_fst.prodMk
        (measurable_snd.add (measurable_const.mul (hW.measurable.comp measurable_fst))))))
  · intro t x
    change ‖β ^ 2 * parisiCDF μ t * v t (x + β * W t)‖ ≤ β ^ 2
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (sq_nonneg β),
      Real.norm_of_nonneg (parisiCDF_nonneg μ t)]
    calc
      _ ≤ β ^ 2 * 1 * 1 := by gcongr; exact parisiCDF_le_one μ t; exact hvbound t _
      _ = _ := by ring
  · intro t
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (β ^ 2 * parisiCDF μ t * v t (x + β * W t))
      (β ^ 2 * parisiCDF μ t * v t (y + β * W t)) ≤ β ^ 2 * dist x y
    rw [dist_eq_norm, ← mul_sub, norm_mul,
      Real.norm_of_nonneg (mul_nonneg (sq_nonneg β) (parisiCDF_nonneg μ t))]
    have hl := (hvlip t).dist_le_mul (x + β * W t) (y + β * W t)
    rw [dist_add_right] at hl
    simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hl
    calc
      _ ≤ (β ^ 2 * 1) * dist x y := by gcongr; exact parisiCDF_le_one μ t; exact hl
      _ = _ := by ring


section ActualState
variable (β h : ℝ) (μ : ParisiMeasure) (v : ℝ → ℝ → ℝ)
    (hv : Continuous (Function.uncurry v)) (hvbound : ∀ t x, ‖v t x‖ ≤ 1)
    (hvlip : ∀ t, LipschitzWith 1 (v t))

/-- The correction is chosen from the actual integral Picard fixed points. -/
def parisiCorrection (T : ℝ) (hT : 0 ≤ T) (W : ℝ → ℝ) (hW : Continuous W) :
    IntegralPicard.Curve hT h (parisiDriftConstant β) :=
  IntegralPicard.solution hT
    (isBoundedMeasurableDrift_parisiNoiseDrift β μ v hv hvbound hvlip W hW)

/-- The actual additive-noise state for arbitrary CDF, on a finite horizon. -/
def parisiStateReal (T : ℝ) (hT : 0 ≤ T) (W : ℝ → ℝ) (hW : Continuous W) (t : ℝ) : ℝ :=
  (parisiCorrection β h μ v hv hvbound hvlip T hT W hW).compProj t + β * W t

theorem continuous_parisiStateReal (T : ℝ) (hT : 0 ≤ T) (W : ℝ → ℝ) (hW : Continuous W) :
    Continuous (parisiStateReal β h μ v hv hvbound hvlip T hT W hW) :=
  ODE.FunSpace.continuous_compProj _ |>.add (hW.const_mul β)

/-- The constructed state satisfies the actual pathwise Lebesgue integral equation. -/
theorem parisiStateReal_integral_equation (T : ℝ) (hT : 0 ≤ T)
    (W : ℝ → ℝ) (hW : Continuous W) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    parisiStateReal β h μ v hv hvbound hvlip T hT W hW t = h + β * W t +
      ∫ s in 0..t, β ^ 2 * parisiCDF μ s *
        v s (parisiStateReal β h μ v hv hvbound hvlip T hT W hW s) := by
  unfold parisiStateReal
  rw [ODE.FunSpace.compProj_of_mem ht]
  have he := IntegralPicard.solution_equation (h := h) hT
    (isBoundedMeasurableDrift_parisiNoiseDrift β μ v hv hvbound hvlip W hW) ⟨t, ht⟩
  change (IntegralPicard.solution (h := h) hT _) ⟨t, ht⟩ + β * W t = _
  rw [he]
  dsimp only [parisiNoiseDrift]
  unfold parisiCorrection
  ring

theorem parisiStateReal_initial (T : ℝ) (hT : 0 ≤ T) (W : ℝ → ℝ) (hW : Continuous W)
    (hW0 : W 0 = 0) : parisiStateReal β h μ v hv hvbound hvlip T hT W hW 0 = h := by
  simpa [hW0] using parisiStateReal_integral_equation β h μ v hv hvbound hvlip T hT W hW ⟨le_rfl, hT⟩

/-- Uniqueness among all continuous states solving the actual integral equation. -/
theorem parisiStateReal_unique (T : ℝ) (hT : 0 ≤ T) (W : ℝ → ℝ) (hW : Continuous W)
    (X : ℝ → ℝ) (hX : Continuous X)
    (hXe : ∀ t ∈ Icc (0 : ℝ) T, X t = h + β * W t +
      ∫ s in 0..t, β ^ 2 * parisiCDF μ s * v s (X s)) :
    EqOn X (parisiStateReal β h μ v hv hvbound hvlip T hT W hW) (Icc (0 : ℝ) T) := by
  let Y := fun t => X t - β * W t
  have hY : Continuous Y := hX.sub (hW.const_mul β)
  have hYe : ∀ t ∈ Icc (0 : ℝ) T, Y t = h + ∫ s in 0..t, parisiNoiseDrift β μ v W s (Y s) := by
    intro t ht
    dsimp only [Y, parisiNoiseDrift]
    simp only [sub_add_cancel]
    rw [hXe t ht]
    ring
  have he := IntegralPicard.real_solution_unique hT
    (isBoundedMeasurableDrift_parisiNoiseDrift β μ v hv hvbound hvlip W hW) Y hY hYe
  intro t ht
  have ht' := he t ht
  change X t - β * W t = _ at ht'
  change X t = _ + β * W t
  dsimp only [parisiCorrection]
  linarith


/-- Exact causality: changing the noise after `r` cannot change the state before `r`. -/
theorem parisiStateReal_causal (T : ℝ) (hT : 0 ≤ T) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T)
    (W Z : ℝ → ℝ) (hW : Continuous W) (hZ : Continuous Z)
    (hnoise : EqOn W Z (Icc (0 : ℝ) r)) :
    EqOn (parisiStateReal β h μ v hv hvbound hvlip T hT W hW)
      (parisiStateReal β h μ v hv hvbound hvlip T hT Z hZ) (Icc (0 : ℝ) r) := by
  have heW := parisiStateReal_unique β h μ v hv hvbound hvlip r hr.1 W hW
    (parisiStateReal β h μ v hv hvbound hvlip T hT W hW)
    (continuous_parisiStateReal β h μ v hv hvbound hvlip T hT W hW)
    (fun t ht => parisiStateReal_integral_equation β h μ v hv hvbound hvlip T hT W hW
      ⟨ht.1, ht.2.trans hr.2⟩)
  have heZ := parisiStateReal_unique β h μ v hv hvbound hvlip r hr.1 W hW
    (parisiStateReal β h μ v hv hvbound hvlip T hT Z hZ)
    (continuous_parisiStateReal β h μ v hv hvbound hvlip T hT Z hZ) (fun t ht => by
      have he := parisiStateReal_integral_equation β h μ v hv hvbound hvlip T hT Z hZ
        ⟨ht.1, ht.2.trans hr.2⟩
      rw [← hnoise ht] at he
      exact he)
  exact fun t ht => (heW ht).trans (heZ ht).symm

end ActualState


section NoisePath
variable (β h : ℝ) (μ : ParisiMeasure) (v : ℝ → ℝ → ℝ)
    (hv : Continuous (Function.uncurry v)) (hvbound : ∀ t x, ‖v t x‖ ≤ 1)
    (hvlip : ∀ t, LipschitzWith 1 (v t))

/-- Constant continuation of a finite continuous noise path. -/
def parisiNoiseExtension {T : ℝ} (hT : 0 ≤ T) (w : C(Icc (0 : ℝ) T, ℝ)) (t : ℝ) : ℝ :=
  w (projIcc 0 T hT t)

@[fun_prop] theorem continuous_parisiNoiseExtension {T : ℝ} (hT : 0 ≤ T)
    (w : C(Icc (0 : ℝ) T, ℝ)) : Continuous (parisiNoiseExtension hT w) :=
  w.continuous.comp continuous_projIcc

/-- The actual state as a map of a finite continuous noise path. -/
def parisiStatePath (T : ℝ) (hT : 0 ≤ T) (w : C(Icc (0 : ℝ) T, ℝ)) : C(Icc (0 : ℝ) T, ℝ) :=
  (parisiCorrection β h μ v hv hvbound hvlip T hT (parisiNoiseExtension hT w)
    (continuous_parisiNoiseExtension hT w)).toContinuousMap + β • w

@[simp] theorem parisiStatePath_apply (T : ℝ) (hT : 0 ≤ T) (w : C(Icc (0 : ℝ) T, ℝ))
    (t : Icc (0 : ℝ) T) :
    parisiStatePath β h μ v hv hvbound hvlip T hT w t =
      parisiStateReal β h μ v hv hvbound hvlip T hT (parisiNoiseExtension hT w)
        (continuous_parisiNoiseExtension hT w) t := by
  simp [parisiStatePath, parisiStateReal, parisiNoiseExtension,
    ODE.FunSpace.compProj_val, projIcc_val]

/-- Changing the noise by a uniform distance changes the drift by at most β³ times that distance. -/
lemma parisiNoiseDrift_noise_dist_le (hvlip : ∀ t, LipschitzWith 1 (v t))
    {T : ℝ} (hT : 0 ≤ T)
    (w z : C(Icc (0 : ℝ) T, ℝ)) (s y : ℝ) :
    dist (parisiNoiseDrift β μ v (parisiNoiseExtension hT w) s y)
      (parisiNoiseDrift β μ v (parisiNoiseExtension hT z) s y) ≤
      β ^ 2 * |β| * dist w z := by
  have hn : ‖parisiNoiseExtension hT w s - parisiNoiseExtension hT z s‖ ≤ dist w z := by
    rw [← dist_eq_norm]
    exact ContinuousMap.dist_apply_le_dist (projIcc 0 T hT s)
  have hl := (hvlip s).dist_le_mul
    (y + β * parisiNoiseExtension hT w s) (y + β * parisiNoiseExtension hT z s)
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, add_sub_add_left_eq_sub,
    ← mul_sub, norm_mul, Real.norm_eq_abs β] at hl
  unfold parisiNoiseDrift
  rw [dist_eq_norm, ← mul_sub, norm_mul,
    Real.norm_of_nonneg (mul_nonneg (sq_nonneg β) (parisiCDF_nonneg μ s))]
  calc
    _ ≤ (β ^ 2 * 1) * (|β| * dist w z) := by gcongr; exact parisiCDF_le_one μ s; exact hl.trans (mul_le_mul_of_nonneg_left hn (abs_nonneg β))
    _ = _ := by ring

/-- The actual state depends Lipschitz continuously on its noise path. -/
theorem exists_lipschitzWith_parisiStatePath (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ≥0, LipschitzWith C (parisiStatePath β h μ v hv hvbound hvlip T hT) := by
  let K := parisiDriftConstant β
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * T)
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hden : 0 < 1 - ((K : ℝ) * T) ^ n / n ! := sub_pos.mpr hn
  let A := IntegralPicard.sensitivity K T n / (1 - ((K : ℝ) * T) ^ n / n !) * (β ^ 2 * |β|) + |β|
  have hA : 0 ≤ A := by
    exact add_nonneg (mul_nonneg (div_nonneg (IntegralPicard.sensitivity_nonneg hT n) hden.le)
      (mul_nonneg (sq_nonneg β) (abs_nonneg β))) (abs_nonneg β)
  refine ⟨⟨A, hA⟩, LipschitzWith.of_dist_le_mul fun w z => ?_⟩
  let hfW := isBoundedMeasurableDrift_parisiNoiseDrift β μ v hv hvbound hvlip
    (parisiNoiseExtension hT w) (continuous_parisiNoiseExtension hT w)
  let hfZ := isBoundedMeasurableDrift_parisiNoiseDrift β μ v hv hvbound hvlip
    (parisiNoiseExtension hT z) (continuous_parisiNoiseExtension hT z)
  have hδ : 0 ≤ β ^ 2 * |β| * dist w z := by positivity
  have hb := IntegralPicard.solution_drift_dist_le (h := h) hT hfW hfZ _ hδ
    (parisiNoiseDrift_noise_dist_le β μ v hvlip hT w z) n hn
  change dist _ _ ≤ A * dist w z
  apply (ContinuousMap.dist_le (mul_nonneg hA dist_nonneg)).mpr
  intro t
  change dist ((IntegralPicard.solution (h := h) hT hfW) t + β * w t)
    ((IntegralPicard.solution (h := h) hT hfZ) t + β * z t) ≤ A * dist w z
  have heval : dist ((IntegralPicard.solution (h := h) hT hfW) t)
      ((IntegralPicard.solution (h := h) hT hfZ) t) ≤ dist
      (IntegralPicard.solution (h := h) hT hfW) (IntegralPicard.solution (h := h) hT hfZ) :=
    ContinuousMap.dist_apply_le_dist (f := ODE.FunSpace.toContinuousMap _) (g := ODE.FunSpace.toContinuousMap _) t
  have hnoise : dist (β * w t) (β * z t) ≤ |β| * dist w z := by
    rw [dist_eq_norm, ← mul_sub, norm_mul, Real.norm_eq_abs β]
    exact mul_le_mul_of_nonneg_left (by simpa only [← dist_eq_norm] using ContinuousMap.dist_apply_le_dist (f := w) (g := z) t) (abs_nonneg β)
  calc
    _ ≤ dist ((IntegralPicard.solution (h := h) hT hfW) t)
        ((IntegralPicard.solution (h := h) hT hfZ) t) + dist (β * w t) (β * z t) := dist_add_add_le _ _ _ _
    _ ≤ IntegralPicard.sensitivity K T n / (1 - ((K : ℝ) * T) ^ n / n !) *
        (β ^ 2 * |β| * dist w z) + |β| * dist w z := add_le_add (heval.trans hb) hnoise
    _ = A * dist w z := by dsimp only [A]; ring

theorem continuous_parisiStatePath (T : ℝ) (hT : 0 ≤ T) :
    Continuous (parisiStatePath β h μ v hv hvbound hvlip T hT) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_parisiStatePath β h μ v hv hvbound hvlip T hT
  exact hC.continuous

theorem measurable_parisiStatePath (T : ℝ) (hT : 0 ≤ T) :
    Measurable (parisiStatePath β h μ v hv hvbound hvlip T hT) :=
  (continuous_parisiStatePath β h μ v hv hvbound hvlip T hT).measurable


/-- Restrict a finite continuous noise path to its past. -/
def parisiNoisePast {T : ℝ} (t : Icc (0 : ℝ) T) (w : C(Icc (0 : ℝ) T, ℝ)) :
    C(Icc (0 : ℝ) (t : ℝ), ℝ) :=
  ⟨fun s => w ⟨s, s.property.1, s.property.2.trans t.property.2⟩,
    w.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

/-- Continue a history constantly to the full time horizon. -/
def parisiPastExtensionPath {T : ℝ} (t : Icc (0 : ℝ) T)
    (w : C(Icc (0 : ℝ) (t : ℝ), ℝ)) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun s => parisiNoiseExtension t.property.1 w s,
    (continuous_parisiNoiseExtension t.property.1 w).comp continuous_subtype_val⟩

lemma lipschitzWith_parisiPastExtensionPath {T : ℝ} (t : Icc (0 : ℝ) T) :
    LipschitzWith 1 (parisiPastExtensionPath t) := by
  apply LipschitzWith.of_dist_le_mul
  intro w z
  norm_num only [NNReal.coe_one, one_mul]
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro s
  exact ContinuousMap.dist_apply_le_dist (f := w) (g := z)
    (projIcc (0 : ℝ) (t : ℝ) t.property.1 (s : ℝ))

/-- State evaluation computed measurably from just the noise history. -/
def parisiEndpointFromPast (T : ℝ) (hT : 0 ≤ T) (t : Icc (0 : ℝ) T)
    (w : C(Icc (0 : ℝ) (t : ℝ), ℝ)) : ℝ :=
  parisiStatePath β h μ v hv hvbound hvlip T hT (parisiPastExtensionPath t w) t

theorem measurable_parisiEndpointFromPast (T : ℝ) (hT : 0 ≤ T) (t : Icc (0 : ℝ) T) :
    Measurable (parisiEndpointFromPast β h μ v hv hvbound hvlip T hT t) :=
  ((ContinuousMap.measurable_eval t).comp
    (measurable_parisiStatePath β h μ v hv hvbound hvlip T hT)).comp
      (lipschitzWith_parisiPastExtensionPath t).continuous.measurable

/-- The actual state evaluation factors exactly through past noise. -/
theorem parisiStatePath_eval_eq_fromPast (T : ℝ) (hT : 0 ≤ T) (t : Icc (0 : ℝ) T)
    (w : C(Icc (0 : ℝ) T, ℝ)) :
    parisiStatePath β h μ v hv hvbound hvlip T hT w t =
      parisiEndpointFromPast β h μ v hv hvbound hvlip T hT t (parisiNoisePast t w) := by
  let W := parisiNoiseExtension hT w
  let z := parisiPastExtensionPath t (parisiNoisePast t w)
  let Z := parisiNoiseExtension hT z
  have hW : Continuous W := continuous_parisiNoiseExtension hT w
  have hZ : Continuous Z := continuous_parisiNoiseExtension hT z
  have hnoise : EqOn W Z (Icc (0 : ℝ) (t : ℝ)) := by
    intro s hs
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans t.property.2⟩
    dsimp [W, Z, z, parisiNoiseExtension, parisiPastExtensionPath, parisiNoisePast]
    simp only [projIcc_of_mem hT hsT]
    change w ⟨s, hsT⟩ = w ⟨(projIcc (0 : ℝ) (t : ℝ) t.property.1 s : ℝ), _⟩
    simp only [projIcc_of_mem t.property.1 hs]
  change parisiStatePath β h μ v hv hvbound hvlip T hT w t =
    parisiStatePath β h μ v hv hvbound hvlip T hT z t
  simp only [parisiStatePath_apply]
  exact parisiStateReal_causal β h μ v hv hvbound hvlip T hT t.property W Z hW hZ hnoise
    ⟨t.property.1, le_rfl⟩

theorem measurable_parisiState_eval_of_measurable_past {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ) (hT : 0 ≤ T) (t : Icc (0 : ℝ) T) (W : Ω → C(Icc (0 : ℝ) T, ℝ))
    (hW : Measurable (fun ω => parisiNoisePast t (W ω))) :
    Measurable (fun ω => parisiStatePath β h μ v hv hvbound hvlip T hT (W ω) t) := by
  simp_rw [parisiStatePath_eval_eq_fromPast]
  exact (measurable_parisiEndpointFromPast β h μ v hv hvbound hvlip T hT t).comp hW

/-- Natural filtration of an arbitrary measurable finite continuous-path noise. -/
def parisiNoiseFiltration {Ω : Type*} [MeasurableSpace Ω] {T : ℝ}
    (W : Ω → C(Icc (0 : ℝ) T, ℝ)) (hW : Measurable W) :
    Filtration (Icc (0 : ℝ) T) (inferInstance : MeasurableSpace Ω) :=
  Filtration.natural (fun t ω => W ω t)
    (fun t => ((ContinuousMap.measurable_eval t).comp hW).stronglyMeasurable)

/-- Genuine adaptedness follows from exact causality and measurable dependence on history. -/
theorem adapted_parisiStatePath {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ) (hT : 0 ≤ T) (W : Ω → C(Icc (0 : ℝ) T, ℝ)) (hW : Measurable W) :
    Adapted (parisiNoiseFiltration W hW)
      (fun t ω => parisiStatePath β h μ v hv hvbound hvlip T hT (W ω) t) := by
  intro t
  let mt : MeasurableSpace Ω := parisiNoiseFiltration W hW t
  letI : MeasurableSpace Ω := mt
  apply measurable_parisiState_eval_of_measurable_past β h μ v hv hvbound hvlip T hT t W
  rw [ContinuousMap.measurable_iff_eval]
  intro s
  let i : Icc (0 : ℝ) T := ⟨s, s.property.1, s.property.2.trans t.property.2⟩
  have hi : i ≤ t := s.property.2
  have hm : Measurable (fun ω => W ω i) := by
    apply measurable_iff_comap_le.mpr
    change MeasurableSpace.comap (fun ω => W ω i) inferInstance ≤ mt
    exact le_iSup₂_of_le i hi le_rfl
  exact hm

end NoisePath

end Paper
