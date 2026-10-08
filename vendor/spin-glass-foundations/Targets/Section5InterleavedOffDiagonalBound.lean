module

public import Targets.Section5InterleavedOffDiagonal

@[expose] public section

set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/- The finite-volume off-diagonal trace/heat estimate.  This is the actual
integrated bound used by the interpolation, not a restatement of a scalar
comparison: the constraint is `u`, while the trial path ends at `v`. -/
theorem section5Interleaved_actualTraceHeat_offDiagonal_le' {k n : ℕ}
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (r : ℕ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
    (u v : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : |v| ∈ Set.Icc (s.q (j - 1)) (s.q j)) {w : ℝ} (hw : w ≤ 1)
    (U : EnergySpace n)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    (1 / (n : ℝ)) *
      (t / 2 * (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
          mixedConstrainedSecond (section5ReverseMode s r j (decide (v < 0)))
            (section5ReverseMass s r j)
            (fun l => section5ReversePathVariance s β t v r j l w)
            (2 * k + 4 + 1) U (sk.hU.w i) (sk.hU.w i) u x y) -
        t * ∑ l : Fin (2 * k + 4 + 1), β ^ 2 *
          (section5InterleavedRho s r j |v| (2 * k + 4 - l + 1) -
            section5InterleavedRho s r j |v| (2 * k + 4 - l)) *
          mixedLevelVarianceD U u
            (section5ReverseMode s r j (decide (v < 0)))
            (section5ReverseMass s r j)
            (fun i => section5ReversePathVariance s β t v r j i w)
            (l : ℕ) (2 * k + 4 + 1 - ((l : ℕ) + 1))
            (section5ReversePathVariance s β t v r j (l : ℕ) w) x y) ≤
      -(2 * t * parisiCorrection s β) +
        t * (β ^ 2 / 2) * (u - v) ^ 2 := by
  let mode := section5ReverseMode s r j (decide (v < 0))
  let m := section5ReverseMass s r j
  let path := fun l => section5ReversePathVariance s β t v r j l w
  let ρ := section5InterleavedRho s r j |v|
  let c := section5InterleavedCross s r hj v
  let μ := fun p => mixedConstrainedReplica mode m path
    (2 * k + 4 - p) (2 * k + 4 + 1 - (2 * k + 4 - p)) U u x y
  have hm : ∀ l, 0 ≤ m l := section5ReverseMass_nonneg s r hj
  have hv0 : ∀ l, 0 ≤ path l := by
    intro l
    exact section5ReversePathVariance_nonneg s β ht hw
      r hj hv l
  have hρ := section5InterleavedRho_endpoints s r hj0 hj |v|
  have hc := section5InterleavedCross_endpoints s r hj0 hj v
  have H := mixedConstrained_trace_sub_heat_eq_covariance_mismatch hn β h sk U t u v
    mode (section5InterleavedMassNat s r j) ρ c path (2 * k + 4)
    (by intro i; rw [← section5ReverseMass_eq_massNat]; exact hm i) hv0
    (section5InterleavedMassNat_endpoints s r hj0 hj).1
    (section5InterleavedMassNat_endpoints s r hj0 hj).2 hρ.1 hc.1
    (by simpa only [show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using hρ.2)
    (by simpa only [show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using hc.2)
    (section5ReverseMode_covariance_increment s r hj v) x y
  have Hc := pairCovarianceExpression_le_mismatch β u v ht.1
    (section5InterleavedMassNat s r j) ρ c (2 * k + 4)
    (section5InterleavedMassNat_endpoints s r hj0 hj).2
    (fun _ hi => section5InterleavedMassNat_mono s r j hi)
    hρ.1 hc.1
    (by simpa only [show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using hρ.2)
    (by simpa only [show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using hc.2)
    μ
    (fun l hl p q => mixedConstrainedReplica_nonneg U u mode m path hm hv0
      (2 * k + 4 - l) (2 * k + 4 + 1 - (2 * k + 4 - l)) x y p q)
    (fun l hl => sum_mixedConstrainedReplica U u mode m path hm hv0
      (2 * k + 4 - l) (2 * k + 4 + 1 - (2 * k + 4 - l)) x y)
  have hmass : m = fun i => section5InterleavedMassNat s r j (2 * k + 4 - i) :=
    funext (section5ReverseMass_eq_massNat s r j)
  dsimp [μ] at Hc
  dsimp [ρ, c] at Hc
  rw [section5InterleavedCross_correction s r hj0 hj β v] at Hc
  rw [← hmass] at H
  calc
    _ = (pairCovarianceExpression β t u (section5InterleavedMassNat s r j) ρ c
        (2 * k + 4) (fun p => mixedConstrainedReplica mode
          m path
          (2 * k + 4 - p) (2 * k + 4 + 1 - (2 * k + 4 - p)) U u x y)) +
        t * β ^ 2 * u * (u - v) := by
      simpa only [mode, m, path, ρ, c, μ] using H
    _ ≤ (-(2 * t * parisiCorrection s β) +
        t * (β ^ 2 / 2) * (v ^ 2 - u ^ 2)) +
        t * β ^ 2 * u * (u - v) := by linarith [Hc]
    _ = _ := by ring

theorem deriv_section5InterleavedInterpolationOffDiagonal_le
    {k n : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) (r : ℕ) {j : ℕ}
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) {t u v w : ℝ}
    (ht : t ∈ Set.Icc 0 1)
    (hv : |v| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    deriv (section5InterleavedInterpolationOffDiagonal n s β h sk.U r j t u v) w ≤
      -(2 * t * parisiCorrection s β) + t * (β ^ 2 / 2) * (u - v) ^ 2 := by
  rw [(hasDerivAt_section5InterleavedInterpolationOffDiagonal hn s β h sk r hj0 hj
    ht hv hw).deriv]
  let N := 2 * k + 4 + 1
  let mode := section5ReverseMode s r j (decide (v < 0))
  let m := section5ReverseMass s r j
  let path := fun l => section5ReversePathVariance s β t v r j l w
  let ρ := section5InterleavedRho s r j |v|
  let a := fun l => β ^ 2 * (ρ (2 * k + 4 - l + 1) - ρ (2 * k + 4 - l))
  let Z := fun ω => Real.sqrt (w * t) • sk.U ω
  let R := fun ω => ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
    mixedConstrainedSecond mode m path N (Z ω) (sk.hU.w i) (sk.hU.w i) u
      (fun _ => h) (fun _ => h)
  let D := fun l : Fin N => fun ω => mixedLevelVarianceD (Z ω) u mode m path l
    (N - (l + 1)) (path l) (fun _ => h) (fun _ => h)
  have hm : ∀ l, 0 ≤ m l := section5ReverseMass_nonneg s r hj
  have hv0 : ∀ l, 0 ≤ path l := by
    intro l
    exact section5ReversePathVariance_nonneg s β ht hw.2.le r hj hv l
  have hZ : Measurable Z := sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))
  have hiR : Integrable R := integrable_mixedConstrainedSecond_SK_trace hn β h sk hZ
    u mode m path hm hv0 N (fun _ => h) (fun _ => h)
  have hiD (l : Fin N) : Integrable (D l) := integrable_mixedLevelVarianceD_all_variances hn hZ
    u mode m path hm hv0 l (N - (l + 1)) (fun _ => h) (fun _ => h)
  have hiS : Integrable (fun ω => ∑ l : Fin N, a l * D l ω) :=
    integrable_finsetSum _ fun l _ => (hiD l).const_mul (a l)
  have hiI : Integrable (fun ω => (1 / (n : ℝ)) *
      (t / 2 * R ω - t * ∑ l : Fin N, a l * D l ω)) := by
    exact (hiR.const_mul (t / 2)).sub (hiS.const_mul t) |>.const_mul (1 / (n : ℝ))
  have hpoint (ω : Ω) :
      (1 / (n : ℝ)) * (t / 2 * R ω - t * ∑ l : Fin N, a l * D l ω) ≤
        -(2 * t * parisiCorrection s β) + t * (β ^ 2 / 2) * (u - v) ^ 2 := by
    simpa only [N, mode, m, path, ρ, a, Z, R, D,
      show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using
      section5Interleaved_actualTraceHeat_offDiagonal_le' hn s β h sk r hj0 hj u v ht hv
        hw.2.le (Z ω) (fun _ => h) (fun _ => h)
  calc
    _ ≤ ∫ _ : Ω, (-(2 * t * parisiCorrection s β) +
        t * (β ^ 2 / 2) * (u - v) ^ 2) :=
      integral_mono hiI (integrable_const _) (fun ω => hpoint ω)
    _ = _ := by simp

theorem section5InterleavedInterpolationOffDiagonal_endpoint_bound
    {k n : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {r : ℕ} (hr0 : 1 ≤ r)
    (hr : r ≤ k + 1) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) {t u v : ℝ}
    (ht : t ∈ Set.Icc 0 1)
    (hv : |v| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      section5InterleavedInterpolationOffDiagonal n s β h sk.U r j t u v 0 -
        2 * t * parisiCorrection s β + t * (β ^ 2 / 2) * (u - v) ^ 2 := by
  have hc := continuousOn_section5InterleavedInterpolationOffDiagonal (s := s) (β := β) (h := h)
    (Z := sk.U) (r := r) (j := j) (t := t) (u := u) (v := v) sk.hU hj ht hv
  have hd : DifferentiableOn ℝ
      (section5InterleavedInterpolationOffDiagonal n s β h sk.U r j t u v)
      (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    exact fun w hw =>
      (hasDerivAt_section5InterleavedInterpolationOffDiagonal (j := j) (t := t)
        (u := u) (v := v) hn s β h sk r hj0 hj ht hv hw).differentiableAt.differentiableWithinAt
  have hb : ∀ w ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv (section5InterleavedInterpolationOffDiagonal n s β h sk.U r j t u v) w ≤
        -(2 * t * parisiCorrection s β) + t * (β ^ 2 / 2) * (u - v) ^ 2 := by
    rw [interior_Icc]
    exact fun w hw => deriv_section5InterleavedInterpolationOffDiagonal_le (j := j)
      (t := t) (u := u) (v := v) (w := w) hn s β h sk r hj0 hj ht hv hw
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  rw [section5InterleavedInterpolationOffDiagonal_one n s β h sk.U hr0 hr j ht.2] at H
  simp only [sub_zero, mul_one] at H
  linarith

theorem constrainedPhi_le_interleavedOffDiagonalMajorant
    {k n : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {r : ℕ} (hr0 : 1 ≤ r)
    (hr : r ≤ k + 1) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
    {t u v ℓ : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : |v| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hatt : ∃ σ τ : Config n, overlap n σ τ = u) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * Real.log 2 + section5InterleavedScalarV s β h r j t v ℓ - ℓ * u -
        2 * t * parisiCorrection s β + t * (β ^ 2 / 2) * (u - v) ^ 2 := by
  obtain ⟨σ, τ, hστ⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n u) := ⟨⟨(σ, τ), hστ⟩⟩
  have hatt' : ∃ σ τ : Config n, overlap n σ τ = u := ⟨σ, τ, hστ⟩
  have H := section5InterleavedInterpolationOffDiagonal_endpoint_bound (j := j)
    (t := t) (u := u) (v := v) hn s β h sk hr0 hr hj0 hj ht hv
  have H0 := section5InterleavedInterpolationOffDiagonal_zero_le_lambda hn s β h sk.U
    r hj ht hv hatt' ℓ
  linarith

end SpinGlass.Targets
