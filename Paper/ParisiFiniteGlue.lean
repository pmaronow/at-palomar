module

public import Paper.ParisiSlabMild
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section

/-! Genuine continuous gluing of the finite Parisi potential and its spatial
derivatives.  The globally clamped functions retain all physical slab values
on `[0,1]`; their gradients are uniformly bounded by one. -/

open Set MeasureTheory ProbabilityTheory Real
open scoped BoundedContinuousFunction

namespace Paper

open SpinGlass SpinGlass.Targets

@[simp] theorem parisiSlabPotential_terminal {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b x : ℝ) :
    parisiSlabPotential s β j m b b x = parisiF s β j x := by
  simp [parisiSlabPotential, parisiStep_zero_var]

@[simp] theorem parisiSlabGradient_terminal {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b x : ℝ) :
    parisiSlabGradient s β j m b b x = parisiFDeriv s β j x := by
  have hd := hasDerivAt_parisiSlabPotential_spatial s β j m b b x
  have he : parisiSlabPotential s β j m b b = parisiF s β j :=
    funext (parisiSlabPotential_terminal s β j m b)
  rw [he] at hd
  exact hd.unique ((parisiF_C2_props s β j).1.1 x)

@[simp] theorem parisiSlabHessian_terminal {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b x : ℝ) :
    parisiSlabHessian s β j m b b x = parisiFSecond s β j x := by
  have hd := hasDerivAt_parisiSlabGradient_spatial s β j m b b x
  have he : parisiSlabGradient s β j m b b = parisiFDeriv s β j :=
    funext (parisiSlabGradient_terminal s β j m b)
  rw [he] at hd
  exact hd.unique ((parisiF_C2_props s β j).1.2.1 x)

noncomputable def parisiFinitePotentialAux {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    ℕ → ℝ → ℝ → ℝ
  | 0 => fun _ => parisiF s β 0
  | j + 1 => fun t x =>
    if t ≤ s.q (k + 2 - j) then
      parisiSlabPotential s β j (s.m (k + 1 - j)) (s.q (k + 2 - j)) t x
    else parisiFinitePotentialAux s β j t x

noncomputable def parisiFiniteGradientAux {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    ℕ → ℝ → ℝ → ℝ
  | 0 => fun _ => parisiFDeriv s β 0
  | j + 1 => fun t x =>
    if t ≤ s.q (k + 2 - j) then
      parisiSlabGradient s β j (s.m (k + 1 - j)) (s.q (k + 2 - j)) t x
    else parisiFiniteGradientAux s β j t x

noncomputable def parisiFiniteHessianAux {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    ℕ → ℝ → ℝ → ℝ
  | 0 => fun _ => parisiFSecond s β 0
  | j + 1 => fun t x =>
    if t ≤ s.q (k + 2 - j) then
      parisiSlabHessian s β j (s.m (k + 1 - j)) (s.q (k + 2 - j)) t x
    else parisiFiniteHessianAux s β j t x

theorem parisiFinitePotentialAux_left {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {j : ℕ} (hj : j ≤ k + 2) (x : ℝ) :
    parisiFinitePotentialAux s β j (s.q (k + 2 - j)) x = parisiF s β j x := by
  cases j with
  | zero => rfl
  | succ j =>
    have he : k + 2 - (j + 1) = k + 1 - j := by omega
    have he' : k + 2 - j = k + 1 - j + 1 := by omega
    have hq : s.q (k + 2 - (j + 1)) ≤ s.q (k + 2 - j) := by
      rw [he, he']
      exact s.q_mono _ (by omega)
    rw [he] at hq
    simp only [parisiFinitePotentialAux, he, ite_eq_left hq, parisiSlabPotential, parisiF]

theorem parisiFiniteAux_C2 {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) (t : ℝ) :
    HasParisiC2 (parisiFinitePotentialAux s β j t)
      (parisiFiniteGradientAux s β j t) (parisiFiniteHessianAux s β j t) := by
  induction j with
  | zero => exact (parisiF_C2_props s β 0).1
  | succ j ih =>
    have hm : s.m (k + 1 - j) ∈ Icc 0 1 :=
      ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
    by_cases ht : t ≤ s.q (k + 2 - j)
    · simpa only [parisiFinitePotentialAux, parisiFiniteGradientAux,
        parisiFiniteHessianAux, ite_eq_left ht] using
        parisiSlab_C2 s β j hm (s.q (k + 2 - j)) t
    · simpa only [parisiFinitePotentialAux, parisiFiniteGradientAux,
        parisiFiniteHessianAux, ite_eq_right ht] using ih

theorem parisiFiniteGradientAux_left {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {j : ℕ} (hj : j ≤ k + 2) (x : ℝ) :
    parisiFiniteGradientAux s β j (s.q (k + 2 - j)) x = parisiFDeriv s β j x := by
  have hd := (parisiFiniteAux_C2 s β j (s.q (k + 2 - j))).1 x
  have he : parisiFinitePotentialAux s β j (s.q (k + 2 - j)) = parisiF s β j :=
    funext (parisiFinitePotentialAux_left s β hj)
  rw [he] at hd
  exact hd.unique ((parisiF_C2_props s β j).1.1 x)

theorem parisiFiniteHessianAux_left {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {j : ℕ} (hj : j ≤ k + 2) (x : ℝ) :
    parisiFiniteHessianAux s β j (s.q (k + 2 - j)) x = parisiFSecond s β j x := by
  have hd := (parisiFiniteAux_C2 s β j (s.q (k + 2 - j))).2.1 x
  have he : parisiFiniteGradientAux s β j (s.q (k + 2 - j)) = parisiFDeriv s β j :=
    funext (parisiFiniteGradientAux_left s β hj)
  rw [he] at hd
  exact hd.unique ((parisiF_C2_props s β j).1.2.1 x)

theorem continuous_parisiFiniteAux {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {j : ℕ} (hj : j ≤ k + 2) :
    Continuous (fun p : ℝ × ℝ => parisiFinitePotentialAux s β j p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => parisiFiniteGradientAux s β j p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => parisiFiniteHessianAux s β j p.1 p.2) := by
  induction j with
  | zero =>
    have hC2 := (parisiF_C2_props s β 0).1
    exact ⟨(continuous_iff_continuousAt.mpr (fun x => (hC2.1 x).continuousAt)).comp continuous_snd,
      (continuous_iff_continuousAt.mpr (fun x => (hC2.2.1 x).continuousAt)).comp continuous_snd,
      (continuous_parisiFSecond s β 0).comp continuous_snd⟩
  | succ j ih =>
    have hj' : j ≤ k + 2 := by omega
    have hc := ih hj'
    have hs := continuous_parisiSlab s β j (s.m_nonneg (p := k + 1 - j) (by omega)) (s.q (k + 2 - j))
    refine ⟨hs.1.if_le hc.1 continuous_fst continuous_const ?_,
      hs.2.1.if_le hc.2.1 continuous_fst continuous_const ?_,
      hs.2.2.if_le hc.2.2 continuous_fst continuous_const ?_⟩
    · intro p hp
      simpa only [hp, parisiSlabPotential_terminal] using
        (parisiFinitePotentialAux_left s β hj' p.2).symm
    · intro p hp
      simpa only [hp, parisiSlabGradient_terminal] using
        (parisiFiniteGradientAux_left s β hj' p.2).symm
    · intro p hp
      simpa only [hp, parisiSlabHessian_terminal] using
        (parisiFiniteHessianAux_left s β hj' p.2).symm

noncomputable def parisiFinitePotential {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  parisiFinitePotentialAux s β (k + 2) (max 0 (min 1 p.1)) p.2

noncomputable def parisiFiniteGradient {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  parisiFiniteGradientAux s β (k + 2) (max 0 (min 1 p.1)) p.2

theorem continuous_parisiFinitePotential {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    Continuous (parisiFinitePotential s β) :=
  (continuous_parisiFiniteAux s β le_rfl).1.comp
    (show Continuous (fun p : ℝ × ℝ => (max 0 (min 1 p.1), p.2)) by fun_prop)

theorem continuous_parisiFiniteGradient {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    Continuous (parisiFiniteGradient s β) :=
  (continuous_parisiFiniteAux s β le_rfl).2.1.comp
    (show Continuous (fun p : ℝ × ℝ => (max 0 (min 1 p.1), p.2)) by fun_prop)

theorem norm_parisiFiniteGradient_le_one {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (p : ℝ × ℝ) : ‖parisiFiniteGradient s β p‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  exact (parisiFiniteAux_C2 s β (k + 2) (max 0 (min 1 p.1))).abs_first_le_one p.2

noncomputable def parisiFiniteGradientBCF {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    (ℝ × ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (parisiFiniteGradient s β)
    (continuous_parisiFiniteGradient s β) 1 (norm_parisiFiniteGradient_le_one s β)

theorem norm_parisiFiniteGradientBCF_le_one {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    ‖parisiFiniteGradientBCF s β‖ ≤ 1 :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ zero_le_one _

theorem parisiFinitePotential_initial {k : ℕ} (s : RSBScheme k) (β x : ℝ) :
    parisiFinitePotential s β (0, x) = parisiF s β (k + 2) x := by
  have he := parisiFinitePotentialAux_left s β (j := k + 2) le_rfl x
  simpa [parisiFinitePotential, s.q_zero] using he

end Paper
