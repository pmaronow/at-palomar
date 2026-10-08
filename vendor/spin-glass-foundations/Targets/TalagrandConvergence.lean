module

public import Targets.TalagrandCore

@[expose] public section

/-!
# The convergence step in Talagrand's Theorem 2.2

This file formalises the deduction on p. 230 of Talagrand, *The Parisi formula*,
Ann. of Math. 163 (2006), from overlap concentration to convergence of the finite
cascade. Concentration is an explicit hypothesis, not an axiom or an established
estimate. The exact unconditional conclusion is obtained downstream in
`Targets.TalagrandTheorem22Integration` and exported under the canonical
`talagrand_theorem_2_2` name by `Targets.TalagrandFinal`.

The interpolation gap is the actual `guerraPsi - guerraPhi`, and its derivative
is the explicit squared-overlap `guerraRemainder` from the completed Theorem 2.1.
The comparison argument only differentiates on the open interval: no derivative
at the singular square-root endpoint `t = 0` is assumed.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass
namespace Targets

universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The nonnegative interpolation gap in (2.20)--(2.22). -/
noncomputable def guerraGap {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) (t : ℝ) : ℝ :=
  guerraPsi s β h t - guerraPhi n s β h U t

theorem guerraGap_zero {n : ℕ} (hn : 0 < n) {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) : guerraGap n s β h U 0 = 0 := by
  simp [guerraGap, guerraPsi, guerraPhi_zero n hn s β h U]

theorem continuousOn_guerraGap {n : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k) :
    ContinuousOn (guerraGap n s β h sk.U) (Set.Icc (0 : ℝ) 1) := by
  have hψ : Continuous (guerraPsi s β h) := by unfold guerraPsi; fun_prop
  exact hψ.continuousOn.sub (continuousOn_guerraPhi β h sk s)

/-- The explicit, rather than existential, remainder is the derivative of the gap. -/
theorem hasDerivAt_guerraGap {n : ℕ} (hn : 0 < n) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (guerraGap n s β h sk.U) (guerraRemainder n s β h sk.U t) t := by
  have hφ : HasDerivAt (guerraPhi n s β h sk.U)
      (-(parisiCorrection s β) - guerraRemainder n s β h sk.U t) t := by
    refine (hasDerivAt_guerraPhi β h sk s ht).congr_deriv ?_
    rw [guerraD_top_expectation hn β h sk s ht,
      guerraRemainder_eq_expansion hn β h sk s ht, parisiCorrection_eq_mass_q]
    have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hnr]
    ring
  have hψ : HasDerivAt (guerraPsi s β h) (-(parisiCorrection s β)) t := by
    convert!
      (hasDerivAt_const t (Real.log 2 + parisiF s β (k + 2) h)).sub
        ((hasDerivAt_id t).mul_const (parisiCorrection s β)) using 1
    simp
  convert! hψ.sub hφ using 1
  simp

theorem guerraGap_nonneg {n : ℕ} (hn : 0 < n) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ guerraGap n s β h sk.U t := by
  have hm : MonotoneOn (guerraGap n s β h sk.U) (Set.Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (continuousOn_guerraGap β h sk s)
    · rw [interior_Icc]
      intro x hx
      exact (hasDerivAt_guerraGap hn β h sk s hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hasDerivAt_guerraGap hn β h sk s hx).deriv]
      exact (guerraRemainder_nonneg_le hn s β h sk.U x).1
  have hh := hm (by simp) ht ht.1
  simpa only [guerraGap_zero hn s β h sk.U] using hh

/-- An endpoint-safe Grönwall estimate for the actual interpolation gap.
The harmless `+1` avoids division by the coefficient, including at `K = 0`. -/
theorem guerraGap_le_mul_exp {n : ℕ} (hn : 0 < n) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    {t₀ K ε : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hbound : ∀ x ∈ Set.Ioo (0 : ℝ) t₀,
      guerraRemainder n s β h sk.U x ≤ K * guerraGap n s β h sk.U x + ε)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) t₀) :
    guerraGap n s β h sk.U t ≤ ε * Real.exp ((K + 1) * t) := by
  let f := guerraGap n s β h sk.U
  let g : ℝ → ℝ := fun x => Real.exp (-(K + 1) * x) * (f x + ε)
  have hsub : Set.Icc (0 : ℝ) t₀ ⊆ Set.Icc (0 : ℝ) 1 :=
    fun x hx => ⟨hx.1, hx.2.trans ht₀.2⟩
  have hf : ContinuousOn f (Set.Icc (0 : ℝ) t₀) :=
    (continuousOn_guerraGap β h sk s).mono hsub
  have hg : ContinuousOn g (Set.Icc (0 : ℝ) t₀) :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (-(K + 1) * x))).continuousOn.mul
      (hf.add continuousOn_const)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) t₀,
      HasDerivAt g (Real.exp (-(K + 1) * x) *
        (guerraRemainder n s β h sk.U x - (K + 1) * (f x + ε))) x := by
    intro x hx
    have hx1 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1, hx.2.trans_le ht₀.2⟩
    convert! (((hasDerivAt_id x).const_mul (-(K + 1))).exp).mul
      ((hasDerivAt_guerraGap hn β h sk s hx1).add_const ε) using 1
    dsimp only [f, id_eq]
    ring
  have hsign : ∀ x ∈ Set.Ioo (0 : ℝ) t₀,
      Real.exp (-(K + 1) * x) *
        (guerraRemainder n s β h sk.U x - (K + 1) * (f x + ε)) ≤ 0 := by
    intro x hx
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have hfn := guerraGap_nonneg hn β h sk s (hsub ⟨hx.1.le, hx.2.le⟩)
    have hb := hbound x hx
    change guerraRemainder n s β h sk.U x - (K + 1) *
      (guerraGap n s β h sk.U x + ε) ≤ 0
    nlinarith [mul_nonneg hK hε]
  have hm : AntitoneOn g (Set.Icc (0 : ℝ) t₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hg
    · rw [interior_Icc]
      exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      exact fun x hx => by rw [(hderiv x hx).deriv]; exact hsign x hx
  have hb : Real.exp (-(K + 1) * t) * (f t + ε) ≤ ε := by
    have hh := hm (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) t₀ from ⟨le_rfl, ht₀.1⟩) ht ht.1
    simpa only [g, f, guerraGap_zero hn s β h sk.U, mul_zero, Real.exp_zero,
      zero_add, one_mul] using hh
  calc
    f t ≤ f t + ε := le_add_of_nonneg_right hε
    _ = Real.exp ((K + 1) * t) * (Real.exp (-(K + 1) * t) * (f t + ε)) := by
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    _ ≤ Real.exp ((K + 1) * t) * ε :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = ε * Real.exp ((K + 1) * t) := mul_comm _ _

/-- Uniform convergence of the gap follows from the differential inequality (2.22).
The coefficient is fixed before the error and the system size are chosen. -/
theorem guerraGap_uniform_of_remainder_control (β h : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    {t₀ K : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1) (hK : 0 ≤ K)
    (hcontrol : ∀ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      guerraRemainder n s β h (sk n).U t ≤ K * guerraGap n s β h (sk n).U t + δ) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (0 : ℝ) t₀,
      |guerraPhi n s β h (sk n).U t - guerraPsi s β h t| < ε := by
  intro ε hε
  let E := Real.exp ((K + 1) * t₀)
  let δ := ε / (E + 1)
  have hE : 0 < E := Real.exp_pos _
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : δ * E < ε := by
    have he : δ * (E + 1) = ε := div_mul_cancel₀ ε (by positivity : E + 1 ≠ 0)
    nlinarith
  filter_upwards [hcontrol δ hδ, eventually_gt_atTop 0] with n hn hpos
  intro t ht
  have hgap := guerraGap_nonneg hpos β h (sk n) s ⟨ht.1, ht.2.trans ht₀.2⟩
  have habs : |guerraPhi n s β h (sk n).U t - guerraPsi s β h t| =
      guerraGap n s β h (sk n).U t := by
    rw [abs_sub_comm, ← guerraGap, abs_of_nonneg hgap]
  rw [habs]
  have hle := guerraGap_le_mul_exp hpos β h (sk n) s ht₀ hK hδ.le hn ht
  have hexp : Real.exp ((K + 1) * t) ≤ E :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by positivity))
  exact (hle.trans (mul_le_mul_of_nonneg_left hexp hδ.le)).trans_lt hδε

/-! ## Bounded observables of the mass-weighted replica distribution -/

theorem guerraReplicaAccum_sub {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {F G : ℕ → Config n → Config n → ℝ} {C D : ℝ}
    (hF : ∀ j σ τ, |F j σ τ| ≤ C) (hG : ∀ j σ τ, |G j σ τ| ≤ D)
    (j : ℕ) (y : Fin n → ℝ) :
    guerraReplicaAccum n s β U h t (fun l σ τ => F l σ τ - G l σ τ) j y =
      guerraReplicaAccum n s β U h t F j y - guerraReplicaAccum n s β U h t G j y := by
  have hb : ∀ (i : Fin 2) l σ τ, |(![F, G] i) l σ τ| ≤ (![C, D] i) := by
    intro i l σ τ
    fin_cases i
    · exact hF l σ τ
    · exact hG l σ τ
  have hh := guerraReplicaAccum_sum_mul n s β U h ht ![1, -1] ![F, G] ![C, D] hb j y
  simpa [Fin.sum_univ_succ, sub_eq_add_neg] using hh

theorem guerraReplicaAccum_mono {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {F G : ℕ → Config n → Config n → ℝ} {C D : ℝ}
    (hF : ∀ j σ τ, |F j σ τ| ≤ C) (hG : ∀ j σ τ, |G j σ τ| ≤ D)
    (hle : ∀ j σ τ, F j σ τ ≤ G j σ τ) (j : ℕ) (y : Fin n → ℝ) :
    guerraReplicaAccum n s β U h t F j y ≤ guerraReplicaAccum n s β U h t G j y := by
  have hh := guerraReplicaAccum_nonneg n s β U h ht
    (K := fun l σ τ => G l σ τ - F l σ τ) (fun l σ τ => sub_nonneg.mpr (hle l σ τ)) j y
  rw [guerraReplicaAccum_sub n s β U h ht hG hF] at hh
  linarith

theorem guerraReplicaAccum_const {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (c : ℝ) (j : ℕ) (y : Fin n → ℝ) :
    guerraReplicaAccum n s β U h t (fun _ _ _ => c) j y = c * (1 - guerraMass s j) := by
  induction j generalizing y with
  | zero => simp [guerraReplicaAccum, guerraMass]
  | succ j ih =>
      rw [guerraReplicaAccum]
      simp_rw [ih, guerraReplicaAvg_const n s β U h ht]
      rw [guerraStepAvg_const n s β U h ⟨ht.1.le, ht.2.le⟩]
      ring

/-- Average a level-dependent two-replica observable over all cascade masses
and over the SK disorder. The total mass is one for `0 < t < 1`. -/
noncomputable def guerraReplicaExpectation {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) (t : ℝ)
    (F : ℕ → Config n → Config n → ℝ) : ℝ :=
  ∫ ω, guerraReplicaAccum n s β (U ω) h t F (k + 2) 0 ∂ℙ

theorem guerraReplicaExpectation_const {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (c : ℝ) :
    guerraReplicaExpectation n s β h U t (fun _ _ _ => c) = c := by
  simp [guerraReplicaExpectation, guerraReplicaAccum_const n s β _ h ht, guerraMass_top]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem guerraReplicaExpectation_nonneg {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {F : ℕ → Config n → Config n → ℝ} (hF : ∀ j σ τ, 0 ≤ F j σ τ) :
    0 ≤ guerraReplicaExpectation n s β h U t F :=
  integral_nonneg fun ω => guerraReplicaAccum_nonneg n s β (U ω) h ht hF (k + 2) 0

theorem guerraReplicaExpectation_mono {n : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {F G : ℕ → Config n → Config n → ℝ} {C D : ℝ}
    (hF : ∀ j σ τ, |F j σ τ| ≤ C) (hG : ∀ j σ τ, |G j σ τ| ≤ D)
    (hle : ∀ j σ τ, F j σ τ ≤ G j σ τ) :
    guerraReplicaExpectation n s β h sk.U t F ≤ guerraReplicaExpectation n s β h sk.U t G :=
  integral_mono (integrable_guerraReplicaAccum β h sk s ht hF (k + 2) 0)
    (integrable_guerraReplicaAccum β h sk s ht hG (k + 2) 0)
    (fun ω => guerraReplicaAccum_mono n s β (sk.U ω) h ht hF hG hle (k + 2) 0)

theorem guerraReplicaExpectation_const_add_mul {n : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (a b : ℝ) {F : ℕ → Config n → Config n → ℝ} {C : ℝ}
    (hF : ∀ j σ τ, |F j σ τ| ≤ C) :
    guerraReplicaExpectation n s β h sk.U t (fun j σ τ => a + b * F j σ τ) =
      a + b * guerraReplicaExpectation n s β h sk.U t F := by
  let Fs : Fin 2 → ℕ → Config n → Config n → ℝ := ![fun _ _ _ => 1, F]
  have hb : ∀ (i : Fin 2) l σ τ, |Fs i l σ τ| ≤ (![1, C] i) := by
    intro i l σ τ
    fin_cases i
    · norm_num [Fs]
    · exact hF l σ τ
  have hp : ∀ U : EnergySpace n,
      guerraReplicaAccum n s β U h t (fun l σ τ => a + b * F l σ τ) (k + 2) 0 =
        a + b * guerraReplicaAccum n s β U h t F (k + 2) 0 := by
    intro U
    have hh := guerraReplicaAccum_sum_mul n s β U h ht ![a, b] Fs ![1, C] hb (k + 2) 0
    simpa [Fs, Fin.sum_univ_succ, guerraReplicaAccum_const n s β U h ht,
      guerraMass_top] using hh
  unfold guerraReplicaExpectation
  simp_rw [hp]
  rw [integral_add (integrable_const a)
    ((integrable_guerraReplicaAccum β h sk s ht hF (k + 2) 0).const_mul b), integral_const_mul]
  simp

/-- The mass-weighted probability of the squared-overlap tail in (2.20).
The reversed index `k + 2 - j` is the same one used by `guerraRemainder`. -/
noncomputable def guerraOverlapTail {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) (t a : ℝ) : ℝ := by
  classical
  exact guerraReplicaExpectation n s β h U t
    (fun j σ τ => if a ≤ (overlap n σ τ - s.q (k + 2 - j)) ^ 2 then 1 else 0)

theorem guerraOverlapTail_mem_Icc {n : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (a : ℝ) :
    guerraOverlapTail n s β h sk.U t a ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  let F : ℕ → Config n → Config n → ℝ := fun j σ τ =>
    if a ≤ (overlap n σ τ - s.q (k + 2 - j)) ^ 2 then 1 else 0
  have hb : ∀ j σ τ, |F j σ τ| ≤ 1 := by
    intro j σ τ
    dsimp [F]
    split_ifs <;> norm_num
  change 0 ≤ guerraReplicaExpectation n s β h sk.U t F ∧
    guerraReplicaExpectation n s β h sk.U t F ≤ 1
  refine ⟨guerraReplicaExpectation_nonneg n s β h sk.U ht (fun j σ τ => ?_), ?_⟩
  · change 0 ≤ (if a ≤ (overlap n σ τ - s.q (k + 2 - j)) ^ 2 then (1 : ℝ) else 0)
    split_ifs <;> norm_num
  · have hh := guerraReplicaExpectation_mono β h sk s ht hb
      (G := fun _ _ _ => 1) (C := 1) (D := 1) (by intros; norm_num)
      (fun j σ τ => (le_abs_self _).trans (hb j σ τ))
    simpa only [guerraReplicaExpectation_const n s β h sk.U ht 1] using hh

/-- The elementary bounded-tail estimate used between (2.20) and (2.22).
All integral comparisons use integrability of the actual cascade observables. -/
theorem guerraRemainder_le_of_overlapTail {n : ℕ} (hn : 0 < n) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {a δ : ℝ} (ha : 0 ≤ a)
    (htail : guerraOverlapTail n s β h sk.U t a ≤ δ) :
    guerraRemainder n s β h sk.U t ≤ (β ^ 2 / 4) * (a + 4 * δ) := by
  classical
  let F : ℕ → Config n → Config n → ℝ := fun j σ τ =>
    if a ≤ (overlap n σ τ - s.q (k + 2 - j)) ^ 2 then 1 else 0
  have hF : ∀ j σ τ, |F j σ τ| ≤ 1 := by
    intro j σ τ
    dsimp [F]
    split_ifs <;> norm_num
  have hG : ∀ j σ τ, |a + 4 * F j σ τ| ≤ a + 4 := by
    intro j σ τ
    calc
      _ ≤ |a| + |4 * F j σ τ| := abs_add_le _ _
      _ ≤ a + 4 := by
        rw [abs_of_nonneg ha, abs_mul, show |(4 : ℝ)| = 4 by norm_num]
        linarith [hF j σ τ]
  have hp : ∀ j σ τ, (overlap n σ τ - s.q (k + 2 - j)) ^ 2 ≤ a + 4 * F j σ τ := by
    intro j σ τ
    have hs := (le_abs_self _).trans (guerra_overlap_sq_le_four hn s j σ τ)
    dsimp [F]
    split_ifs with he
    · linarith
    · simp only [mul_zero, add_zero]
      exact (lt_of_not_ge he).le
  have he := guerraReplicaExpectation_mono β h sk s ht (guerra_overlap_sq_le_four hn s) hG hp
  rw [guerraReplicaExpectation_const_add_mul β h sk s ht a 4 hF] at he
  change guerraReplicaExpectation n s β h sk.U t F ≤ δ at htail
  rw [guerraRemainder, if_pos ht]
  change (β ^ 2 / 4) * guerraReplicaExpectation n s β h sk.U t
    (fun j σ τ => (overlap n σ τ - s.q (k + 2 - j)) ^ 2) ≤ _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- The differential-inequality conclusion of the overlap-concentration estimate. -/
theorem guerraRemainder_le_of_overlap_concentration {n : ℕ} (hn : 0 < n) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {K η : ℝ} (hK : 0 ≤ K) (hη : 0 ≤ η)
    (htail : guerraOverlapTail n s β h sk.U t
      (K * guerraGap n s β h sk.U t + η) ≤ η) :
    guerraRemainder n s β h sk.U t ≤
      ((β ^ 2 / 4) * K) * guerraGap n s β h sk.U t + (5 * β ^ 2 / 4) * η := by
  have ha := add_nonneg (mul_nonneg hK
    (guerraGap_nonneg hn β h sk s ⟨ht.1.le, ht.2.le⟩)) hη
  have hh := guerraRemainder_le_of_overlapTail hn β h sk s ht ha htail
  nlinarith only [hh]

/-! ## The convergence conclusion, conditional only on the stated concentration bound -/

/-- The mass-weighted form of Proposition 2.3 implies uniform convergence on
`[0,t₀]`. The concentration coefficient may depend on the scheme, but not on
`N`, `t`, or the error `η`. No positivity of individual scheme masses is assumed. -/
theorem guerraPhi_uniform_of_overlap_concentration (β h : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    {t₀ K : ℝ} (ht₀ : t₀ ∈ Set.Ico (0 : ℝ) 1) (hK : 0 ≤ K)
    (hconcentration : ∀ η > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      guerraOverlapTail n s β h (sk n).U t
        (K * guerraGap n s β h (sk n).U t + η) ≤ η) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (0 : ℝ) t₀,
      |guerraPhi n s β h (sk n).U t - guerraPsi s β h t| < ε := by
  apply guerraGap_uniform_of_remainder_control β h sk s ⟨ht₀.1, ht₀.2.le⟩
    (K := (β ^ 2 / 4) * K) (mul_nonneg (by positivity) hK)
  intro δ hδ
  let L := 5 * β ^ 2 / 4
  let η := δ / (L + 1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hη : 0 < η := div_pos hδ (by positivity)
  have hsmall : L * η ≤ δ := by
    have he : η * (L + 1) = δ := div_mul_cancel₀ δ (by positivity : L + 1 ≠ 0)
    nlinarith
  filter_upwards [hconcentration η hη, eventually_gt_atTop 0] with n hn hpos
  intro t ht
  have ht1 : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2⟩
  have hh := guerraRemainder_le_of_overlap_concentration hpos β h (sk n) s ht1 hK hη.le (hn t ht)
  exact hh.trans (add_le_add le_rfl hsmall)

theorem guerraPhi_tendsto_of_overlap_concentration (β h : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    {t₀ K : ℝ} (ht₀ : t₀ ∈ Set.Ico (0 : ℝ) 1) (hK : 0 ≤ K)
    (hconcentration : ∀ η > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      guerraOverlapTail n s β h (sk n).U t
        (K * guerraGap n s β h (sk n).U t + η) ≤ η)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) t₀) :
    Tendsto (fun n => guerraPhi n s β h (sk n).U t) atTop (𝓝 (guerraPsi s β h t)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [guerraPhi_uniform_of_overlap_concentration β h sk s ht₀ hK hconcentration ε hε]
    with n hn
  simpa only [Real.dist_eq] using hn t ht

/-- The precise quantifiers of Theorem 2.2, conditional on the mass-weighted
overlap-concentration estimate for near-optimal fixed-level minimizers.
Proving this hypothesis (including schemes with coincident levels) remains open. -/
theorem talagrand_theorem_2_2_of_overlap_concentration (β h : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h) {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hconcentration : ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k),
      parisiFunctional s β h ≤ parisiValue β h + ε →
      (∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) →
      ∃ K ≥ (0 : ℝ), ∀ η > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
        guerraOverlapTail n s β h (sk n).U t
          (K * guerraGap n s β h (sk n).U t + η) ≤ η) :
    ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k),
      parisiFunctional s β h ≤ parisiValue β h + ε →
      (∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) →
      ∀ t, 0 ≤ t → t ≤ t₀ →
        Tendsto (fun n => guerraPhi n s β h (sk n).U t) atTop (𝓝 (guerraPsi s β h t)) := by
  obtain ⟨ε, hε, hc⟩ := hconcentration
  refine ⟨ε, hε, fun s hs hmin t ht0 htt₀ => ?_⟩
  obtain ⟨K, hK, htail⟩ := hc s hs hmin
  exact guerraPhi_tendsto_of_overlap_concentration β h sk s ⟨ht0.trans htt₀, ht₀⟩ hK htail
    ⟨ht0, htt₀⟩

end Targets
end SpinGlass
