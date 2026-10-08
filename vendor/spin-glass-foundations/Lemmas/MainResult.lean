module

public import Lemmas.AT.Definitions
public import Lemmas.Cavity.TalagrandCavity
public import Lemmas.Concentration.Weak
public import Lemmas.SmartPath.Interpolation

@[expose] public section

/-!
# Quantitative strict Almeida--Thouless result

This fixed public entry module assembles the AT parameter theory, concentration,
cavity estimates, Guerra--Talagrand bounds, and smart-path estimates used by
`Main.lean`.
-/


open MeasureTheory ProbabilityTheory Real BigOperators Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SpinGlass.AT

universe u

private theorem gibbs_average_n_det_mono
    {N n : ℕ} (H : SpinGlass.EnergySpace N)
    {f g : SpinGlass.ReplicaFun N n} (hfg : ∀ σs, f σs ≤ g σs) :
    SpinGlass.gibbs_average_n_det (N := N) (n := n) H f ≤
      SpinGlass.gibbs_average_n_det (N := N) (n := n) H g := by
  unfold SpinGlass.gibbs_average_n_det
  apply Finset.sum_le_sum
  intro σs _
  exact mul_le_mul_of_nonneg_right (hfg σs)
    (Finset.prod_nonneg fun i _ =>
      SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σs i))

private theorem gibbs_average_n_det_linear
    {N n : ℕ} (H : SpinGlass.EnergySpace N)
    (a b : ℝ) (f g : SpinGlass.ReplicaFun N n) :
    SpinGlass.gibbs_average_n_det (N := N) (n := n) H
        (fun σs => a * f σs + b * g σs) =
      a * SpinGlass.gibbs_average_n_det (N := N) (n := n) H f +
        b * SpinGlass.gibbs_average_n_det (N := N) (n := n) H g := by
  unfold SpinGlass.gibbs_average_n_det
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σs _
  ring

private theorem thirdMoment_eq_twoReplica
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} [NeZero N] {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) :
    thirdMoment path s =
      SpinGlass.nu
        (N := N) (β := β) (h := h) (q := q)
        (sk := path.sk) (sim := path.simple) 2 s
        (fun σs => |SpinGlass.overlap N (σs 0) (σs 1) - q| ^ 3) := by
  unfold thirdMoment quenchedReplicaAverage SpinGlass.nu SpinGlass.gibbs_average_n
  apply integral_congr_ae
  filter_upwards with ω
  change replicaGibbsAverage (fullPathHamiltonian path s ω)
      (fun σs : Replicas N 4 => |centeredOverlap q σs 0 1| ^ 3) =
    SpinGlass.gibbs_average_n_det (N := N) (n := 2)
      (fullPathHamiltonian path s ω)
      (fun σs => |SpinGlass.overlap N (σs 0) (σs 1) - q| ^ 3)
  exact fourReplica_firstPair_eq_two (fullPathHamiltonian path s ω) q
    (fun x => |x| ^ 3)

private theorem quenchedTail_eq_twoReplica
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} [NeZero N] {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s eps : ℝ) :
    quenchedTail path s eps =
      SpinGlass.nu
        (N := N) (β := β) (h := h) (q := q)
        (sk := path.sk) (sim := path.simple) 2 s
        (fun σs => if eps ≤
          |SpinGlass.overlap N (σs 0) (σs 1) - q| then 1 else 0) := by
  unfold quenchedTail quenchedReplicaAverage SpinGlass.nu SpinGlass.gibbs_average_n
  apply integral_congr_ae
  filter_upwards with ω
  change replicaGibbsAverage (fullPathHamiltonian path s ω)
      (fun σs : Replicas N 4 =>
        if eps ≤ |centeredOverlap q σs 0 1| then 1 else 0) =
    SpinGlass.gibbs_average_n_det (N := N) (n := 2)
      (fullPathHamiltonian path s ω)
      (fun σs => if eps ≤
        |SpinGlass.overlap N (σs 0) (σs 1) - q| then 1 else 0)
  exact fourReplica_firstPair_eq_two (fullPathHamiltonian path s ω) q
    (fun x => if eps ≤ |x| then 1 else 0)

private theorem thirdMoment_split
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} [NeZero N] {β h q s eps : ℝ}
    (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hq : q ∈ Set.Icc (0 : ℝ) 1) (heps : 0 ≤ eps) :
    thirdMoment path s ≤ eps * A path s + 8 * quenchedTail path s eps := by
  rw [thirdMoment_eq_twoReplica, A_eq_overlapVariance,
    quenchedTail_eq_twoReplica]
  unfold SpinGlass.GeneralizedLatala.overlapVariance SpinGlass.nu
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  rw [← MeasureTheory.integral_add
    ((SpinGlass.integrable_gibbs_average_n
      (N := N) (β := β) (h := h) (q := q)
      (sk := path.sk) (sim := path.simple) 2 s
      (SpinGlass.GeneralizedLatala.centeredOverlapSq N q)).const_mul eps)
    ((SpinGlass.integrable_gibbs_average_n
      (N := N) (β := β) (h := h) (q := q)
      (sk := path.sk) (sim := path.simple) 2 s
      (fun σs => if eps ≤
        |SpinGlass.overlap N (σs 0) (σs 1) - q| then 1 else 0)).const_mul 8)]
  apply integral_mono
  · exact SpinGlass.integrable_gibbs_average_n
      (N := N) (β := β) (h := h) (q := q)
      (sk := path.sk) (sim := path.simple) 2 s _
  · exact ((SpinGlass.integrable_gibbs_average_n
      (N := N) (β := β) (h := h) (q := q)
      (sk := path.sk) (sim := path.simple) 2 s
      (SpinGlass.GeneralizedLatala.centeredOverlapSq N q)).const_mul eps).add
      ((SpinGlass.integrable_gibbs_average_n
        (N := N) (β := β) (h := h) (q := q)
        (sk := path.sk) (sim := path.simple) 2 s
        (fun σs => if eps ≤
          |SpinGlass.overlap N (σs 0) (σs 1) - q| then 1 else 0)).const_mul 8)
  · intro ω
    change SpinGlass.gibbs_average_n_det (N := N) (n := 2)
        (fullPathHamiltonian path s ω)
        (fun σs => |SpinGlass.overlap N (σs 0) (σs 1) - q| ^ 3) ≤
      eps * SpinGlass.gibbs_average_n_det (N := N) (n := 2)
        (fullPathHamiltonian path s ω)
        (SpinGlass.GeneralizedLatala.centeredOverlapSq N q) +
      8 * SpinGlass.gibbs_average_n_det (N := N) (n := 2)
        (fullPathHamiltonian path s ω)
        (fun σs => if eps ≤
          |SpinGlass.overlap N (σs 0) (σs 1) - q| then 1 else 0)
    rw [← gibbs_average_n_det_linear]
    apply gibbs_average_n_det_mono
    intro σs
    show
        |SpinGlass.overlap N (σs 0) (σs 1) - q| ^ 3 ≤
          eps * (SpinGlass.overlap N (σs 0) (σs 1) - q) ^ 2 +
            8 * (if eps ≤ |SpinGlass.overlap N (σs 0) (σs 1) - q| then 1 else 0)
    ·
      let x := |SpinGlass.overlap N (σs 0) (σs 1) - q|
      have hx0 : 0 ≤ x := abs_nonneg _
      have hx2 : x ≤ 2 := by
        have hover : SpinGlass.overlap N (σs 0) (σs 1) ∈ Set.Icc (-1 : ℝ) 1 := by
          apply attainableOverlap_mem_Icc hN
          simp only [attainableOverlaps, Finset.mem_image]
          exact ⟨(σs 0, σs 1), Finset.mem_univ _, rfl⟩
        rw [abs_le]
        constructor <;> linarith [hover.1, hover.2, hq.1, hq.2]
      by_cases htail : eps ≤ x
      · rw [if_pos htail]
        have hxSq : x ^ 2 ≤ 4 := by nlinarith [sq_nonneg x]
        have hxCube : x ^ 3 ≤ 8 := by
          calc
            x ^ 3 = x * x ^ 2 := by ring
            _ ≤ 2 * x ^ 2 := mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)
            _ ≤ 8 := by linarith
        dsimp [x] at hxCube ⊢
        nlinarith [mul_nonneg heps (sq_nonneg
          (SpinGlass.overlap N (σs 0) (σs 1) - q))]
      · rw [if_neg htail]
        have hxeps : x ≤ eps := (lt_of_not_ge htail).le
        dsimp [x] at hxeps ⊢
        have hsquare : 0 ≤
            |SpinGlass.overlap N (σs 0) (σs 1) - q| ^ 2 := sq_nonneg _
        calc
          |SpinGlass.overlap N (σs 0) (σs 1) - q| ^ 3 =
              |SpinGlass.overlap N (σs 0) (σs 1) - q| *
                |SpinGlass.overlap N (σs 0) (σs 1) - q| ^ 2 := by ring
          _ ≤ eps * |SpinGlass.overlap N (σs 0) (σs 1) - q| ^ 2 :=
            mul_le_mul_of_nonneg_right hxeps hsquare
          _ = eps * (SpinGlass.overlap N (σs 0) (σs 1) - q) ^ 2 + 8 * 0 := by
            rw [sq_abs]
            ring

private theorem nat_mul_rpow_neg_three_halves_tendsto_zero :
    Tendsto (fun N : ℕ => (N : ℝ) * (N : ℝ) ^ (-(3 : ℝ) / 2))
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hsqrt
  convert hinv using 1
  funext N
  by_cases hN : N = 0
  · simp [hN]
  · have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    calc
      (N : ℝ) * (N : ℝ) ^ (-(3 : ℝ) / 2) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(3 : ℝ) / 2) := by
            rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) + (-(3 : ℝ) / 2)) :=
        (Real.rpow_add hNr 1 (-(3 : ℝ) / 2)).symm
      _ = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by norm_num
      _ = ((N : ℝ) ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hNr.le (1 / 2)
      _ = (Real.sqrt (N : ℝ))⁻¹ := by rw [Real.sqrt_eq_rpow]

private theorem nat_mul_exp_neg_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-c * (N : ℝ)))
      atTop (nhds 0) := by
  have hcN : Tendsto (fun N : ℕ => c * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hmain := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hcN
  have hcconst : Tendsto (fun _ : ℕ => c⁻¹) atTop (nhds c⁻¹) :=
    tendsto_const_nhds
  have hscaled := hcconst.mul hmain
  convert hscaled using 1
  · funext N
    field_simp [hc.ne']
    congr 1 <;> ring_nf
  · norm_num

/--
Do not edit this claim even if you have any reason
--/

structure QuantitativeATConclusion {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] (K : Set (ℝ × ℝ)) : Prop where
  secondMoment :
    ∃ M, 0 ≤ M ∧ ∀ {N : ℕ}, 0 < N → ∀ {β h q s : ℝ},
      (β, h) ∈ K → q = rsQ β h → s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ path : RSSmartPathDisorder Ω N β h q, N * A path s ≤ M
  freeEnergy :
    ∃ M, 0 ≤ M ∧ ∀ {N : ℕ}, 0 < N → ∀ {β h q : ℝ},
      (β, h) ∈ K → q = rsQ β h →
      ∀ path : RSSmartPathDisorder Ω N β h q,
      0 ≤ rsFreeEnergy β h - skFreeEnergy path ∧
      rsFreeEnergy β h - skFreeEnergy path ≤ M / N
  replicon :
    ∀ eps > 0, ∃ N0, ∀ {N : ℕ}, N0 ≤ N → ∀ {β h q s : ℝ},
      (β, h) ∈ K → q = rsQ β h → s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ path : RSSmartPathDisorder Ω N β h q,
      |N * (A path s - 2 * B path s + C path s) -
        rsA β h / (1 - s * atParameter β h)| < eps

/-- Quantitative strict-AT theorem with all analytic inputs supplied by named
lemmas rather than project-specific typeclass assumptions. -/
theorem quantitative_strictAT {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (K : Set (ℝ × ℝ))
    (data : UniformATData K) :
    QuantitativeATConclusion (Ω := Ω) K := by
  obtain ⟨Cpre, hCpre, hpre⟩ :=
    exists_hasCavityPreAbsorptionBound (Ω := Ω) data
  let split : ℝ := 1 / (2 * Cpre)
  have hsplit : 0 < split := by dsimp [split]; positivity
  obtain ⟨c, hc, Ctail, hCtail, htail⟩ :=
    overlap_tail (Omega := Ω) data hsplit
  let M : ℝ := 2 * Cpre + 16 * Cpre * Ctail / c
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hSecond :
      ∀ {N : ℕ}, 0 < N → ∀ {β h q s : ℝ},
        (β, h) ∈ K → q = rsQ β h → s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ path : RSSmartPathDisorder Ω N β h q, N * A path s ≤ M := by
    intro N hN β h q s hK hq hs path
    subst q
    letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have htail' : quenchedTail path s split ≤
        Ctail * Real.exp (-c * (N : ℝ)) := by
      rw [quenchedTail_eq_twoReplica]
      exact htail hN hK ⟨s, hs⟩ path
    have hthird := thirdMoment_split (s := s) (eps := split)
      path hN (rsQ_mem_Icc β h) hsplit.le
    have hpre' := hpre hN hK rfl hs path
    have hexpInv : Real.exp (-c * (N : ℝ)) ≤ 1 / (c * (N : ℝ)) := by
      have hcn : 0 < c * (N : ℝ) := mul_pos hc hNr
      have hlin : c * (N : ℝ) ≤ Real.exp (c * (N : ℝ)) := by
        linarith [Real.add_one_le_exp (c * (N : ℝ))]
      simpa [one_div, Real.exp_neg] using
        one_div_le_one_div_of_le hcn hlin
    have hexpN : (N : ℝ) * Real.exp (-c * (N : ℝ)) ≤ 1 / c := by
      calc
        (N : ℝ) * Real.exp (-c * (N : ℝ)) ≤
            (N : ℝ) * (1 / (c * (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hexpInv hNr.le
        _ = 1 / c := by field_simp [hc.ne', hNr.ne']
    have htailN : (N : ℝ) * quenchedTail path s split ≤ Ctail / c := by
      calc
        (N : ℝ) * quenchedTail path s split ≤
            (N : ℝ) * (Ctail * Real.exp (-c * (N : ℝ))) :=
          mul_le_mul_of_nonneg_left htail' hNr.le
        _ = Ctail * ((N : ℝ) * Real.exp (-c * (N : ℝ))) := by ring
        _ ≤ Ctail * (1 / c) := mul_le_mul_of_nonneg_left hexpN hCtail.le
        _ = Ctail / c := by ring
    have hthirdN : (N : ℝ) * thirdMoment path s ≤
        split * ((N : ℝ) * A path s) + 8 * (Ctail / c) := by
      calc
        (N : ℝ) * thirdMoment path s ≤
            (N : ℝ) * (split * A path s + 8 * quenchedTail path s split) :=
          mul_le_mul_of_nonneg_left hthird hNr.le
        _ = split * ((N : ℝ) * A path s) +
            8 * ((N : ℝ) * quenchedTail path s split) := by ring
        _ ≤ split * ((N : ℝ) * A path s) + 8 * (Ctail / c) := by
          gcongr
    have hpreN : (N : ℝ) * A path s ≤
        Cpre + Cpre * ((N : ℝ) * thirdMoment path s) := by
      calc
        (N : ℝ) * A path s ≤
            (N : ℝ) * (Cpre / (N : ℝ) + Cpre * thirdMoment path s) :=
          mul_le_mul_of_nonneg_left hpre' hNr.le
        _ = Cpre + Cpre * ((N : ℝ) * thirdMoment path s) := by
          field_simp [hNr.ne']
    have hcoef : Cpre * split = 1 / 2 := by
      dsimp [split]
      field_simp [hCpre.ne']
    have hcombined : (N : ℝ) * A path s ≤
        Cpre + (Cpre * split) * ((N : ℝ) * A path s) +
          8 * Cpre * (Ctail / c) := by
      calc
        (N : ℝ) * A path s ≤
            Cpre + Cpre * ((N : ℝ) * thirdMoment path s) := hpreN
        _ ≤ Cpre + Cpre *
            (split * ((N : ℝ) * A path s) + 8 * (Ctail / c)) :=
          by
            simpa [add_comm] using
              add_le_add_left (mul_le_mul_of_nonneg_left hthirdN hCpre.le) Cpre
        _ = Cpre + (Cpre * split) * ((N : ℝ) * A path s) +
            8 * Cpre * (Ctail / c) := by ring
    rw [hcoef] at hcombined
    calc
      (N : ℝ) * A path s ≤ 2 * (Cpre + 8 * Cpre * (Ctail / c)) := by
        nlinarith [hcombined]
      _ = M := by dsimp [M]; ring
  refine
    { secondMoment := ⟨M, hM, hSecond⟩
      freeEnergy := ?_
      replicon := ?_ }
  · let Mf : ℝ := data.βmax ^ 2 / 4 * M
    have hMf : 0 ≤ Mf := by dsimp [Mf]; positivity
    refine ⟨Mf, hMf, ?_⟩
    intro N hN β h q hK hq path
    subst q
    letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hsum := SpinGlass.GeneralizedLatala.replica_symmetric_sum_rule
      (N := N) (β := β) (h := h) (q := rsQ β h)
      (sk := path.sk) (sim := path.simple)
      hN (rsQ_mem_Icc β h).1 path.independent
    have hfreeId :
        rsFreeEnergy β h - skFreeEnergy path =
          SpinGlass.GeneralizedLatala.rsPressure β h (rsQ β h) -
            SpinGlass.GeneralizedLatala.interpolatedPressure
              (N := N) (β := β) (h := h) (q := rsQ β h)
              (sk := path.sk) (sim := path.simple) 1 := by
      unfold rsFreeEnergy skFreeEnergy rsPathValue pathFreeEnergy
        SpinGlass.GeneralizedLatala.rsPressure
        SpinGlass.GeneralizedLatala.interpolatedPressure
        SpinGlass.AT.standardGaussianExpectation
        SpinGlass.GeneralizedLatala.standardGaussianExpectation
      congr 1
      ring
    have hvar0 : ∀ t : ℝ, 0 ≤
        SpinGlass.GeneralizedLatala.overlapVariance
          (N := N) (β := β) (h := h) (q := rsQ β h)
          (sk := path.sk) (sim := path.simple) t :=
      fun t => SpinGlass.GeneralizedLatala.overlapVariance_nonneg
        (N := N) (β := β) (h := h) (q := rsQ β h)
        (sk := path.sk) (sim := path.simple) t
    have hint0 : 0 ≤ ∫ t in Set.Icc (0 : ℝ) 1,
        SpinGlass.GeneralizedLatala.overlapVariance
          (N := N) (β := β) (h := h) (q := rsQ β h)
          (sk := path.sk) (sim := path.simple) t := integral_nonneg hvar0
    have hvarBound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        SpinGlass.GeneralizedLatala.overlapVariance
          (N := N) (β := β) (h := h) (q := rsQ β h)
          (sk := path.sk) (sim := path.simple) t ≤ M / (N : ℝ) := by
      intro t ht
      rw [← A_eq_overlapVariance path t]
      apply (le_div_iff₀ hNr).2
      simpa [mul_comm] using hSecond hN hK rfl ht path
    have hconstInt : IntegrableOn (fun _ : ℝ => M / (N : ℝ))
        (Set.Icc (0 : ℝ) 1) (volume : Measure ℝ) :=
      integrableOn_const (hs := by rw [Real.volume_Icc]; finiteness)
    have hintBound : (∫ t in Set.Icc (0 : ℝ) 1,
        SpinGlass.GeneralizedLatala.overlapVariance
          (N := N) (β := β) (h := h) (q := rsQ β h)
          (sk := path.sk) (sim := path.simple) t) ≤ M / (N : ℝ) := by
      calc
        _ ≤ ∫ _t in Set.Icc (0 : ℝ) 1, M / (N : ℝ) :=
          integral_mono_ae hsum.1 hconstInt
            (ae_restrict_of_forall_mem measurableSet_Icc hvarBound)
        _ = M / (N : ℝ) := by
          norm_num [MeasureTheory.integral_const, Measure.restrict_apply_univ,
            Real.volume_Icc]
    have hβsq : β ^ 2 ≤ data.βmax ^ 2 := by
      have hβpos := data.β_pos (β, h) hK
      have hβmax := data.β_bound (β, h) hK
      nlinarith [mul_nonneg (sub_nonneg.mpr hβmax)
        (add_nonneg data.βmax_pos.le hβpos.le)]
    have hMN : 0 ≤ M / (N : ℝ) := div_nonneg hM hNr.le
    constructor
    · rw [hfreeId, hsum.2]
      exact mul_nonneg (by positivity) hint0
    · rw [hfreeId, hsum.2]
      calc
        (β ^ 2 / 4) * ∫ t in Set.Icc (0 : ℝ) 1,
            SpinGlass.GeneralizedLatala.overlapVariance
              (N := N) (β := β) (h := h) (q := rsQ β h)
              (sk := path.sk) (sim := path.simple) t ≤
            (β ^ 2 / 4) * (M / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hintBound (by positivity)
        _ ≤ (data.βmax ^ 2 / 4) * (M / (N : ℝ)) := by
          gcongr
        _ = Mf / (N : ℝ) := by dsimp [Mf]; ring
  · obtain ⟨Cmode, hCmode, hmodeBound⟩ :=
      cavityModeRemainder_bound_from_lastSpin (Ω := Ω) data
    intro target htarget
    let eta : ℝ := target * data.gap / (4 * Cmode * (M + 1))
    have heta : 0 < eta := by
      dsimp [eta]
      exact div_pos (mul_pos htarget data.gap_pos)
        (mul_pos (mul_pos (by norm_num) hCmode) (by linarith [hM]))
    obtain ⟨ct, hct, Ct, hCt, htailEta⟩ :=
      overlap_tail (Omega := Ω) data heta
    let delta : ℝ :=
      target * data.gap / (4 * Cmode * (1 + 8 * Ct))
    have hdelta : 0 < delta := by
      dsimp [delta]
      exact div_pos (mul_pos htarget data.gap_pos)
        (mul_pos (mul_pos (by norm_num) hCmode) (by linarith [hCt]))
    obtain ⟨Nr, hNr⟩ :=
      (Metric.tendsto_atTop.1 nat_mul_rpow_neg_three_halves_tendsto_zero)
        delta hdelta
    obtain ⟨Ne, hNe⟩ :=
      (Metric.tendsto_atTop.1 (nat_mul_exp_neg_tendsto_zero ct hct))
        delta hdelta
    let N0 : ℕ := max 1 (max Nr Ne)
    refine ⟨N0, ?_⟩
    intro N hN0 β h q s hK hq hs path
    subst q
    have hN : 0 < N := lt_of_lt_of_le (by
      have : 1 ≤ N0 := le_max_left _ _
      exact this) hN0
    letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
    have hNrPos : (0 : ℝ) < N := by exact_mod_cast hN
    have hNrIndex : Nr ≤ N :=
      le_trans (le_trans (le_max_left Nr Ne) (le_max_right 1 (max Nr Ne))) hN0
    have hNeIndex : Ne ≤ N :=
      le_trans (le_trans (le_max_right Nr Ne) (le_max_right 1 (max Nr Ne))) hN0
    have hrSmall : (N : ℝ) * (N : ℝ) ^ (-(3 : ℝ) / 2) < delta := by
      have hd := hNr N hNrIndex
      rw [Real.dist_eq, sub_zero, abs_of_nonneg
        (mul_nonneg hNrPos.le (Real.rpow_nonneg hNrPos.le _))] at hd
      exact hd
    have heSmall : (N : ℝ) * Real.exp (-ct * (N : ℝ)) < delta := by
      have hd := hNe N hNeIndex
      simpa [Real.dist_eq, abs_of_nonneg
        (mul_nonneg hNrPos.le (Real.exp_nonneg _))] using hd
    have htail' : quenchedTail path s eta ≤
        Ct * Real.exp (-ct * (N : ℝ)) := by
      rw [quenchedTail_eq_twoReplica]
      exact htailEta hN hK ⟨s, hs⟩ path
    have hthird := thirdMoment_split (s := s) (eps := eta)
      path hN (rsQ_mem_Icc β h) heta.le
    have htailN : (N : ℝ) * quenchedTail path s eta ≤
        Ct * ((N : ℝ) * Real.exp (-ct * (N : ℝ))) := by
      calc
        (N : ℝ) * quenchedTail path s eta ≤
            (N : ℝ) * (Ct * Real.exp (-ct * (N : ℝ))) :=
          mul_le_mul_of_nonneg_left htail' hNrPos.le
        _ = Ct * ((N : ℝ) * Real.exp (-ct * (N : ℝ))) := by ring
    have hthirdN : (N : ℝ) * thirdMoment path s ≤
        eta * M + 8 * Ct *
          ((N : ℝ) * Real.exp (-ct * (N : ℝ))) := by
      calc
        (N : ℝ) * thirdMoment path s ≤
            (N : ℝ) * (eta * A path s + 8 * quenchedTail path s eta) :=
          mul_le_mul_of_nonneg_left hthird hNrPos.le
        _ = eta * ((N : ℝ) * A path s) +
            8 * ((N : ℝ) * quenchedTail path s eta) := by ring
        _ ≤ eta * M + 8 *
            (Ct * ((N : ℝ) * Real.exp (-ct * (N : ℝ)))) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hSecond hN hK rfl hs path) heta.le)
            (mul_le_mul_of_nonneg_left htailN (by norm_num))
        _ = eta * M + 8 * Ct *
            ((N : ℝ) * Real.exp (-ct * (N : ℝ))) := by ring
    let R : Fin 3 → ℝ :=
      cavityChangeMatrix.mulVec (cavityRemainder path s)
    have hRnorm : ‖R‖ ≤ Cmode *
        ((N : ℝ) ^ (-(3 : ℝ) / 2) + thirdMoment path s) := by
      simpa [R, cavityErrorScale] using hmodeBound hN hK rfl hs path
    have hRcomp : |R 2| ≤ Cmode *
        ((N : ℝ) ^ (-(3 : ℝ) / 2) + thirdMoment path s) := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm R 2).trans hRnorm
    have hmodeEq := cavityChangeMatrix_mulVec_cavityRemainder (s := s) path
    have hReq : R 2 = cavityD path s -
        s * β ^ 2 * rsA β h * cavityD path s -
          (1 / (N : ℝ)) * rsA β h := by
      simpa [R, rsA] using congrFun hmodeEq (2 : Fin 3)
    have hα0 : 0 ≤ atParameter β h := by
      rw [atParameter_eq_beta_sq_mul_gaussian_sech_fourth
        (data.β_pos (β, h) hK) (data.h_pos (β, h) hK)]
      exact mul_nonneg (sq_nonneg β)
        (integral_nonneg fun z => by positivity)
    have hden : data.gap ≤ 1 - s * atParameter β h := by
      have hsα := mul_le_of_le_one_left hα0 hs.2
      linarith [data.strictAT (β, h) hK]
    have hdenPos : 0 < 1 - s * atParameter β h :=
      data.gap_pos.trans_le hden
    have hDeq : (1 - s * atParameter β h) * cavityD path s =
        rsA β h / (N : ℝ) + R 2 := by
      rw [hReq]
      unfold atParameter
      ring
    have htargetEq :
        (N : ℝ) * cavityD path s -
            rsA β h / (1 - s * atParameter β h) =
          ((N : ℝ) * R 2) / (1 - s * atParameter β h) := by
      apply (eq_div_iff hdenPos.ne').2
      rw [sub_mul, div_mul_cancel₀ _ hdenPos.ne']
      calc
        (N : ℝ) * cavityD path s * (1 - s * atParameter β h) - rsA β h =
            (N : ℝ) * ((1 - s * atParameter β h) * cavityD path s) -
              rsA β h := by ring
        _ = (N : ℝ) * (rsA β h / (N : ℝ) + R 2) - rsA β h := by
          rw [hDeq]
        _ = (N : ℝ) * R 2 := by
          field_simp [hNrPos.ne']; ring
    have herrorBound :
        |(N : ℝ) * cavityD path s -
            rsA β h / (1 - s * atParameter β h)| ≤
          (Cmode / data.gap) *
            ((N : ℝ) * (N : ℝ) ^ (-(3 : ℝ) / 2) +
              (N : ℝ) * thirdMoment path s) := by
      rw [htargetEq, abs_div, abs_mul, abs_of_pos hNrPos,
        abs_of_pos hdenPos]
      have hnum : (N : ℝ) * |R 2| ≤
          (N : ℝ) * (Cmode *
            ((N : ℝ) ^ (-(3 : ℝ) / 2) + thirdMoment path s)) :=
        mul_le_mul_of_nonneg_left hRcomp hNrPos.le
      have herr0 : 0 ≤
          (N : ℝ) ^ (-(3 : ℝ) / 2) + thirdMoment path s :=
        add_nonneg (Real.rpow_nonneg hNrPos.le _) (thirdMoment_nonneg path s)
      have hnum0 : 0 ≤ (N : ℝ) * (Cmode *
          ((N : ℝ) ^ (-(3 : ℝ) / 2) + thirdMoment path s)) := by
        exact mul_nonneg hNrPos.le (mul_nonneg hCmode.le herr0)
      calc
        (N : ℝ) * |R 2| / (1 - s * atParameter β h) ≤
            ((N : ℝ) * (Cmode *
              ((N : ℝ) ^ (-(3 : ℝ) / 2) + thirdMoment path s))) /
                data.gap := div_le_div₀ hnum0 hnum data.gap_pos hden
        _ = (Cmode / data.gap) *
            ((N : ℝ) * (N : ℝ) ^ (-(3 : ℝ) / 2) +
              (N : ℝ) * thirdMoment path s) := by ring
    have hscaledExp : 8 * Ct *
        ((N : ℝ) * Real.exp (-ct * (N : ℝ))) < 8 * Ct * delta :=
      mul_lt_mul_of_pos_left heSmall (mul_pos (by norm_num) hCt)
    have hseq :
        (N : ℝ) * (N : ℝ) ^ (-(3 : ℝ) / 2) +
            (N : ℝ) * thirdMoment path s <
          eta * M + (1 + 8 * Ct) * delta := by
      nlinarith [hrSmall, hthirdN, hscaledExp]
    have hetaPart :
        (Cmode / data.gap) * (eta * M) < target / 4 := by
      have hratio : M / (M + 1) < 1 := by
        apply (div_lt_one (by linarith [hM])).2
        linarith
      have heq : (Cmode / data.gap) * (eta * M) =
          target / 4 * (M / (M + 1)) := by
        dsimp [eta]
        field_simp [hCmode.ne', data.gap_pos.ne']
      rw [heq]
      exact mul_lt_of_lt_one_right (by positivity) hratio
    have hdeltaPart :
        (Cmode / data.gap) * ((1 + 8 * Ct) * delta) = target / 4 := by
      dsimp [delta]
      field_simp [hCmode.ne', data.gap_pos.ne']
    have hcoefPos : 0 < Cmode / data.gap := div_pos hCmode data.gap_pos
    calc
      |(N : ℝ) * (A path s - 2 * B path s + C path s) -
          rsA β h / (1 - s * atParameter β h)| =
          |(N : ℝ) * cavityD path s -
            rsA β h / (1 - s * atParameter β h)| := by
        rfl
      _ ≤ (Cmode / data.gap) *
            ((N : ℝ) * (N : ℝ) ^ (-(3 : ℝ) / 2) +
              (N : ℝ) * thirdMoment path s) := herrorBound
      _ < (Cmode / data.gap) *
            (eta * M + (1 + 8 * Ct) * delta) :=
        mul_lt_mul_of_pos_left hseq hcoefPos
      _ = (Cmode / data.gap) * (eta * M) +
            (Cmode / data.gap) * ((1 + 8 * Ct) * delta) := by ring
      _ < target / 4 + target / 4 := by rw [hdeltaPart]; linarith
      _ < target := by linarith

/-- The quantitative theorem with the uniform numerical data extracted from
compactness.  Keeping this construction here leaves public entry modules free
of the compactness and empty-set bookkeeping. -/
theorem quantitative_strictAT_on_compact {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (K : Set (ℝ × ℝ)) (hKcompact : IsCompact K)
    (hKsub : K ⊆ strictATRegion) :
    QuantitativeATConclusion (Ω := Ω) K := by
  by_cases hKne : K.Nonempty
  · obtain ⟨pβ, hpβ, hβmax⟩ :=
      hKcompact.exists_isMaxOn hKne
        (continuousOn_fst : ContinuousOn (fun p : ℝ × ℝ => p.1) K)
    have hqcont : ContinuousOn
        (fun p : ℝ × ℝ => rsQ p.1 p.2) K :=
      (continuousOn_rsParameters_of_subset_strictATRegion hKsub).1
    obtain ⟨pq, hpq, hqmin⟩ := hKcompact.exists_isMinOn hKne hqcont
    obtain ⟨gap, hgap_pos, hgap_lower⟩ :=
      exists_uniform_at_gap_on_compact hKcompact hKne hKsub
    let data : UniformATData K :=
      { isCompact := hKcompact
        βmax := pβ.1
        qmin := rsQ pq.1 pq.2
        gap := gap
        βmax_pos := (hKsub hpβ).1
        qmin_pos := rsQ_pos (hKsub hpq).1 (hKsub hpq).2.1
        gap_pos := hgap_pos
        β_pos := fun p hp => (hKsub hp).1
        h_pos := fun p hp => (hKsub hp).2.1
        β_bound := fun p hp => hβmax hp
        q_lower := fun p hp => hqmin hp
        strictAT := by
          intro p hp
          have hgap := hgap_lower p hp
          linarith }
    exact quantitative_strictAT K data
  · let data : UniformATData K :=
      { isCompact := hKcompact
        βmax := 1
        qmin := 1
        gap := 1
        βmax_pos := by norm_num
        qmin_pos := by norm_num
        gap_pos := by norm_num
        β_pos := fun p hp => (hKsub hp).1
        h_pos := fun p hp => (hKsub hp).2.1
        β_bound := by
          intro p hp
          exact (hKne ⟨p, hp⟩).elim
        q_lower := by
          intro p hp
          exact (hKne ⟨p, hp⟩).elim
        strictAT := by
          intro p hp
          exact (hKne ⟨p, hp⟩).elim }
    exact quantitative_strictAT K data


end SpinGlass.AT
