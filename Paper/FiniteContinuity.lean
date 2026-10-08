module

public import Paper.FiniteSK
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-!
# Uniform continuity of finite SK free energies

The parameter comparison is uniform in the number of spins. The random energy
envelope is a logarithm of two finite Gaussian partition functions. Jensen and
the exact Gaussian exponential moments bound its expectation linearly in the
number of sites.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Paper

@[simp] theorem spinSign_sq (s : Bool) : spinSign s ^ 2 = 1 := by
  cases s <;> norm_num [spinSign]

@[simp] theorem abs_spinSign (s : Bool) : |spinSign s| = 1 := by
  cases s <;> norm_num [spinSign]

theorem abs_spin_sum_le (n : ℕ) (σ : SKConfiguration n) :
    |∑ i : Fin n, spinSign (σ i)| ≤ n := by
  simpa using Finset.abs_sum_le_sum_abs (s := Finset.univ) (fun i : Fin n => spinSign (σ i))

theorem skHamiltonian_eq_linear {n : ℕ} (β h : ℝ) (g : SKCouplings n)
    (σ : SKConfiguration n) :
    skHamiltonian β h g σ = β * skHamiltonian 1 0 g σ +
      h * ∑ i : Fin n, spinSign (σ i) := by
  unfold skHamiltonian
  ring

/-- Exact independent-Gaussian exponential moment for each configuration. -/
theorem integral_exp_skHamiltonian {n : ℕ} (β h : ℝ) (σ : SKConfiguration n) :
    (∫ g : SKCouplings n, Real.exp (skHamiltonian β h g σ) ∂skCouplingLaw n) =
      Real.exp (h * ∑ i : Fin n, spinSign (σ i) +
        (Fintype.card (SKEdge n) : ℝ) * (β / Real.sqrt n) ^ 2 / 2) := by
  let a : SKEdge n → ℝ := fun ij =>
    β / Real.sqrt n * spinSign (σ ij.val.1) * spinSign (σ ij.val.2)
  have heq : (fun g : SKCouplings n => Real.exp (skHamiltonian β h g σ)) =
      fun g => Real.exp (h * ∑ i : Fin n, spinSign (σ i)) *
        ∏ ij : SKEdge n, Real.exp (a ij * g ij) := by
    ext g
    have hH : skHamiltonian β h g σ = h * ∑ i : Fin n, spinSign (σ i) +
        ∑ ij : SKEdge n, a ij * g ij := by
      unfold skHamiltonian
      rw [Finset.mul_sum, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro ij _
      dsimp [a]
      ring
    rw [hH, Real.exp_add, Real.exp_sum]
  rw [heq, integral_const_mul]
  unfold skCouplingLaw
  rw [integral_fintype_prod_eq_prod (fun ij : SKEdge n => fun x : ℝ => Real.exp (a ij * x))]
  have hmgf : ∀ ij : SKEdge n,
      (∫ x, Real.exp (a ij * x) ∂gaussianReal 0 1) = Real.exp (a ij ^ 2 / 2) := by
    intro ij
    simpa [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (a ij)
  simp_rw [hmgf]
  rw [← Real.exp_sum, ← Real.exp_add]
  congr 1
  have ha : ∀ ij : SKEdge n, a ij ^ 2 = (β / Real.sqrt n) ^ 2 := by
    intro ij
    simp [a, mul_pow]
  simp_rw [ha]
  simp
  ring

private theorem log_sum_exp_le_of_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (H K : ι → ℝ) (D : ℝ) (hb : ∀ i, H i ≤ K i + D) :
    Real.log (∑ i, Real.exp (H i)) ≤ Real.log (∑ i, Real.exp (K i)) + D := by
  have hK : 0 < ∑ i, Real.exp (K i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hH : 0 < ∑ i, Real.exp (H i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hz : (∑ i, Real.exp (H i)) ≤ Real.exp D * ∑ i, Real.exp (K i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have he := Real.exp_le_exp.mpr (hb i)
    simpa [Real.exp_add, mul_comm] using he
  have hl := Real.log_le_log hH hz
  rw [Real.log_mul (Real.exp_pos D).ne' hK.ne', Real.log_exp] at hl
  linarith

theorem abs_log_sum_exp_sub_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (H K : ι → ℝ) (D : ℝ) (hb : ∀ i, |H i - K i| ≤ D) :
    |Real.log (∑ i, Real.exp (H i)) - Real.log (∑ i, Real.exp (K i))| ≤ D := by
  have hHK := log_sum_exp_le_of_le H K D (fun i => by
    have hh := (abs_le.mp (hb i)).2
    linarith)
  have hKH := log_sum_exp_le_of_le K H D (fun i => by
    have hh := (abs_le.mp (hb i)).1
    linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

noncomputable def skEnergyEnvelope {n : ℕ} (g : SKCouplings n) : ℝ :=
  Real.log (skPartitionFunction 1 0 g + skPartitionFunction (-1) 0 g)

theorem skEnergyEnvelope_ge_abs {n : ℕ} (g : SKCouplings n) (σ : SKConfiguration n) :
    |skHamiltonian 1 0 g σ| ≤ skEnergyEnvelope g := by
  have hZp := skPartitionFunction_pos (n := n) 1 0 g
  have hZn := skPartitionFunction_pos (n := n) (-1) 0 g
  have hHp := exp_skHamiltonian_le_partition (n := n) 1 0 g σ
  have hHn := exp_skHamiltonian_le_partition (n := n) (-1) 0 g σ
  have hneg : skHamiltonian (-1) 0 g σ = -skHamiltonian 1 0 g σ := by
    rw [skHamiltonian_eq_linear (-1) 0]
    ring
  have hp := Real.log_le_log (Real.exp_pos (skHamiltonian 1 0 g σ))
    (hHp.trans (le_add_of_nonneg_right hZn.le))
  have hn := Real.log_le_log (Real.exp_pos (skHamiltonian (-1) 0 g σ))
    (hHn.trans (le_add_of_nonneg_left hZp.le))
  rw [Real.log_exp] at hp hn
  rw [hneg] at hn
  exact abs_le.mpr ⟨by dsimp [skEnergyEnvelope]; linarith, hp⟩

theorem skEnergyEnvelope_nonneg {n : ℕ} (g : SKCouplings n) : 0 ≤ skEnergyEnvelope g :=
  (abs_nonneg _).trans (skEnergyEnvelope_ge_abs g (fun _ => true))

theorem integrable_skEnergyEnvelope (n : ℕ) :
    Integrable (@skEnergyEnvelope n) (skCouplingLaw n) := by
  have hi := (integrable_skPartitionFunction (n := n) 1 0).add
    (integrable_skPartitionFunction (n := n) (-1) 0)
  apply hi.mono'
  · exact (((continuous_skPartitionFunction (n := n) 1 0).add
      (continuous_skPartitionFunction (n := n) (-1) 0)).log
      (fun g => (add_pos (skPartitionFunction_pos 1 0 g)
        (skPartitionFunction_pos (-1) 0 g)).ne')).aestronglyMeasurable
  · filter_upwards with g
    change ‖skEnergyEnvelope g‖ ≤ skPartitionFunction 1 0 g + skPartitionFunction (-1) 0 g
    rw [Real.norm_eq_abs, abs_of_nonneg (skEnergyEnvelope_nonneg g)]
    exact (Real.log_le_sub_one_of_pos (add_pos (skPartitionFunction_pos 1 0 g)
      (skPartitionFunction_pos (-1) 0 g))).trans (by linarith)

theorem abs_log_skPartitionFunction_parameters {n : ℕ} (β h β' h' : ℝ)
    (g : SKCouplings n) :
    |Real.log (skPartitionFunction β h g) - Real.log (skPartitionFunction β' h' g)| ≤
      |β - β'| * skEnergyEnvelope g + |h - h'| * n := by
  apply abs_log_sum_exp_sub_le
  intro σ
  rw [skHamiltonian_eq_linear β h, skHamiltonian_eq_linear β' h']
  calc
    |β * skHamiltonian 1 0 g σ + h * ∑ i, spinSign (σ i) -
        (β' * skHamiltonian 1 0 g σ + h' * ∑ i, spinSign (σ i))| =
      |(β - β') * skHamiltonian 1 0 g σ + (h - h') * ∑ i, spinSign (σ i)| := by
        congr 1
        ring
    _ ≤ |(β - β') * skHamiltonian 1 0 g σ| +
        |(h - h') * ∑ i, spinSign (σ i)| := abs_add_le _ _
    _ = |β - β'| * |skHamiltonian 1 0 g σ| +
        |h - h'| * |∑ i, spinSign (σ i)| := by rw [abs_mul, abs_mul]
    _ ≤ |β - β'| * skEnergyEnvelope g + |h - h'| * n :=
      add_le_add (mul_le_mul_of_nonneg_left (skEnergyEnvelope_ge_abs g σ) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (abs_spin_sum_le n σ) (abs_nonneg _))

theorem card_skEdge_le_square (n : ℕ) : Fintype.card (SKEdge n) ≤ n ^ 2 := by
  have hc := Fintype.card_subtype_le (fun ij : Fin n × Fin n => ij.1 < ij.2)
  simpa [sq] using hc

theorem skVarianceProxy_le {n : ℕ} (hn : 0 < n) :
    (Fintype.card (SKEdge n) : ℝ) * (1 / Real.sqrt n) ^ 2 / 2 ≤ (n : ℝ) / 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (Fintype.card (SKEdge n) : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast card_skEdge_le_square n
  rw [div_pow, one_pow, Real.sq_sqrt hnpos.le]
  have heq : (Fintype.card (SKEdge n) : ℝ) * (1 / (n : ℝ)) / 2 =
      (Fintype.card (SKEdge n) : ℝ) / (2 * n) := by ring
  rw [heq]
  apply (div_le_iff₀ (mul_pos (by norm_num) hnpos)).mpr
  nlinarith

theorem integral_skPartitionFunction_le {n : ℕ} (hn : 0 < n) :
    (∫ g : SKCouplings n, skPartitionFunction 1 0 g ∂skCouplingLaw n) ≤
      (2 : ℝ) ^ n * Real.exp ((n : ℝ) / 2) := by
  unfold skPartitionFunction
  rw [integral_finsetSum Finset.univ (fun σ _ => integrable_exp_skHamiltonian (n := n) 1 0 σ)]
  simp_rw [integral_exp_skHamiltonian, zero_mul, zero_add]
  have he := Finset.sum_le_sum (s := Finset.univ) (fun (σ : SKConfiguration n) (_ : σ ∈ Finset.univ) =>
    Real.exp_le_exp.mpr (skVarianceProxy_le hn))
  simpa using he

private theorem integral_skPartitionFunction_neg_eq (n : ℕ) :
    (∫ g : SKCouplings n, skPartitionFunction (-1) 0 g ∂skCouplingLaw n) =
      ∫ g : SKCouplings n, skPartitionFunction 1 0 g ∂skCouplingLaw n := by
  unfold skPartitionFunction
  rw [integral_finsetSum Finset.univ (fun σ _ => integrable_exp_skHamiltonian (n := n) (-1) 0 σ),
    integral_finsetSum Finset.univ (fun σ _ => integrable_exp_skHamiltonian (n := n) 1 0 σ)]
  apply Finset.sum_congr rfl
  intro σ _
  rw [integral_exp_skHamiltonian, integral_exp_skHamiltonian]
  congr 1
  ring

noncomputable def skParameterLipschitz : ℝ := 2 * Real.log 2 + 1 / 2

theorem skParameterLipschitz_pos : 0 < skParameterLipschitz := by
  have hp := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold skParameterLipschitz
  linarith

/-- The Gaussian envelope's expected size grows at most linearly in `n`. -/
theorem integral_skEnergyEnvelope_le {n : ℕ} (hn : 0 < n) :
    (∫ g : SKCouplings n, skEnergyEnvelope g ∂skCouplingLaw n) ≤
      n * skParameterLipschitz := by
  let W : SKCouplings n → ℝ := fun g => skPartitionFunction 1 0 g +
    skPartitionFunction (-1) 0 g
  have hiW : Integrable W (skCouplingLaw n) :=
    (integrable_skPartitionFunction 1 0).add (integrable_skPartitionFunction (-1) 0)
  have hpos : ∀ g, 0 < W g := fun g => add_pos (skPartitionFunction_pos 1 0 g)
    (skPartitionFunction_pos (-1) 0 g)
  have hW1 : ∀ g, 1 ≤ W g := by
    intro g
    have he := skEnergyEnvelope_nonneg g
    change 0 ≤ Real.log (W g) at he
    exact (Real.log_nonneg_iff (hpos g)).mp he
  have hj := ((strictConcaveOn_log_Ioi.concaveOn).subset
    (fun x hx => lt_of_lt_of_le (by norm_num) hx) (convex_Ici (1 : ℝ))).le_map_integral
    (Real.continuousOn_log.mono (fun x hx => ne_of_gt (lt_of_lt_of_le (by norm_num) hx)))
    isClosed_Ici (Filter.Eventually.of_forall hW1) hiW (integrable_skEnergyEnvelope n)
  have heW : (∫ g, W g ∂skCouplingLaw n) ≤
      2 * (2 : ℝ) ^ n * Real.exp ((n : ℝ) / 2) := by
    change (∫ g : SKCouplings n, skPartitionFunction 1 0 g +
      skPartitionFunction (-1) 0 g ∂skCouplingLaw n) ≤ _
    rw [integral_add (integrable_skPartitionFunction 1 0) (integrable_skPartitionFunction (-1) 0),
      integral_skPartitionFunction_neg_eq]
    linarith [integral_skPartitionFunction_le hn]
  have hiWpos : 0 < ∫ g, W g ∂skCouplingLaw n := by
    have he := integral_mono (integrable_const (1 : ℝ)) hiW hW1
    have hge : 1 ≤ ∫ g, W g ∂skCouplingLaw n := by simpa using he
    linarith
  have hl := Real.log_le_log hiWpos heW
  have hexp : Real.log (2 * (2 : ℝ) ^ n * Real.exp ((n : ℝ) / 2)) =
      ((n : ℝ) + 1) * Real.log 2 + (n : ℝ) / 2 := by
    rw [Real.log_mul (mul_pos (by norm_num) (pow_pos (by norm_num) n)).ne'
      (Real.exp_pos _).ne', Real.log_mul (by norm_num) (pow_pos (by norm_num) n).ne',
      Real.log_exp, Real.log_pow]
    ring
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [hexp] at hl
  change (∫ g, skEnergyEnvelope g ∂skCouplingLaw n) ≤ Real.log (∫ g, W g ∂skCouplingLaw n) at hj
  unfold skParameterLipschitz
  nlinarith [mul_nonneg (sub_nonneg.mpr hn1) hp]

/-- Parameter continuity has a constant independent of the system size. -/
theorem finiteSKFreeEnergy_parameters_lipschitz (β h β' h' : ℝ) (n : ℕ) :
    |finiteSKFreeEnergy β h n - finiteSKFreeEnergy β' h' n| ≤
      skParameterLipschitz * |β - β'| + |h - h'| := by
  by_cases hn0 : n = 0
  · subst n
    simp only [finiteSKFreeEnergy_zero, sub_self, abs_zero]
    exact add_nonneg (mul_nonneg skParameterLipschitz_pos.le (abs_nonneg _)) (abs_nonneg _)
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  let f : SKCouplings n → ℝ := fun g => Real.log (skPartitionFunction β h g) -
    Real.log (skPartitionFunction β' h' g)
  have hi : Integrable f (skCouplingLaw n) :=
    (integrable_log_skPartitionFunction β h).sub (integrable_log_skPartitionFunction β' h')
  have hD : Integrable (fun g : SKCouplings n =>
      |β - β'| * skEnergyEnvelope g + |h - h'| * n) (skCouplingLaw n) :=
    ((integrable_skEnergyEnvelope n).const_mul _).add (integrable_const _)
  have he := integral_mono hi.abs hD (abs_log_skPartitionFunction_parameters β h β' h')
  have hDf : (∫ g : SKCouplings n, |β - β'| * skEnergyEnvelope g + |h - h'| * n
      ∂skCouplingLaw n) =
      |β - β'| * (∫ g : SKCouplings n, skEnergyEnvelope g ∂skCouplingLaw n) +
        |h - h'| * n := by
    rw [integral_add ((integrable_skEnergyEnvelope n).const_mul _) (integrable_const _),
      integral_const_mul]
    simp
  rw [hDf] at he
  have hsize := integral_skEnergyEnvelope_le hn
  have hbound : |∫ g, f g ∂skCouplingLaw n| ≤
      |β - β'| * (n * skParameterLipschitz) + |h - h'| * n :=
    (abs_integral_le_integral_abs (f := f) (μ := skCouplingLaw n)).trans (he.trans
      (add_le_add (mul_le_mul_of_nonneg_left hsize (abs_nonneg (β - β'))) le_rfl))
  have hdiff : finiteSKFreeEnergy β h n - finiteSKFreeEnergy β' h' n =
      (1 / (n : ℝ)) * ∫ g, f g ∂skCouplingLaw n := by
    unfold finiteSKFreeEnergy f
    rw [integral_sub (integrable_log_skPartitionFunction β h)
      (integrable_log_skPartitionFunction β' h')]
    ring
  rw [hdiff, abs_mul, abs_of_pos (one_div_pos.mpr hnpos)]
  calc
    (1 / (n : ℝ)) * |∫ g, f g ∂skCouplingLaw n| ≤
        (1 / (n : ℝ)) * (|β - β'| * (n * skParameterLipschitz) + |h - h'| * n) :=
      mul_le_mul_of_nonneg_left hbound (one_div_nonneg.mpr hnpos.le)
    _ = skParameterLipschitz * |β - β'| + |h - h'| := by
      field_simp [hnpos.ne']

end Paper
