module

public import Targets.Section5PairScalarComparison
public import Targets.Section5Interleaving

@[expose] public section

/-!
# Genuine mixed Gaussian cascades for Proposition 5.11

Levels are numbered from the terminal function outwards. An independent step
uses two independent Gaussian coordinates; shared and opposite steps use one.
The scalar comparison doubles the raw mass precisely at the two shared modes.
No ordering of the modes is imposed by the definitions.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators

namespace SpinGlass.Targets

inductive Section5GaussianMode where
  | independent
  | shared
  | opposite
  deriving DecidableEq

def Section5GaussianMode.scalarMass : Section5GaussianMode → ℝ → ℝ
  | .independent, m => m
  | .shared, m => 2*m
  | .opposite, m => 2*m

variable {P : Type*}

noncomputable def mixedScalarCascade (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) : ℕ → P → ℝ → ℝ × ℝ → ℝ
  | 0 => fun _ l x => coupledSite l x.1 x.2
  | j+1 => match mode j with
    | .independent =>
      GTFrame.finiteStep (gaussianReal 0 1) (m j) (fun p => Real.sqrt (v j p)) (fun _ => 0)
        (GTFrame.finiteStep (gaussianReal 0 1) (m j) (fun _ => 0)
          (fun p => Real.sqrt (v j p)) (mixedScalarCascade mode m v j))
    | .shared => GTFrame.finiteStep (gaussianReal 0 1) (m j)
        (fun p => Real.sqrt (v j p)) (fun p => Real.sqrt (v j p)) (mixedScalarCascade mode m v j)
    | .opposite => GTFrame.finiteStep (gaussianReal 0 1) (m j)
        (fun p => Real.sqrt (v j p)) (fun p => -Real.sqrt (v j p)) (mixedScalarCascade mode m v j)

noncomputable def mixedScalarCascadeD (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) : ℕ → P → ℝ → ℝ × ℝ → ℝ
  | 0 => fun _ l x => GTFrame.fLbaseD l x
  | j+1 => match mode j with
    | .independent =>
      GTFrame.finiteStepD (gaussianReal 0 1) (m j) (fun p => Real.sqrt (v j p)) (fun _ => 0)
        (GTFrame.finiteStep (gaussianReal 0 1) (m j) (fun _ => 0)
          (fun p => Real.sqrt (v j p)) (mixedScalarCascade mode m v j))
        (GTFrame.finiteStepD (gaussianReal 0 1) (m j) (fun _ => 0)
          (fun p => Real.sqrt (v j p)) (mixedScalarCascade mode m v j)
            (mixedScalarCascadeD mode m v j))
    | .shared => GTFrame.finiteStepD (gaussianReal 0 1) (m j)
        (fun p => Real.sqrt (v j p)) (fun p => Real.sqrt (v j p))
          (mixedScalarCascade mode m v j) (mixedScalarCascadeD mode m v j)
    | .opposite => GTFrame.finiteStepD (gaussianReal 0 1) (m j)
        (fun p => Real.sqrt (v j p)) (fun p => -Real.sqrt (v j p))
          (mixedScalarCascade mode m v j) (mixedScalarCascadeD mode m v j)

/-- Matching actual vector recursion, with an arbitrary terminal function.
This permits later constrained-terminal transport without redefining the levels. -/
noncomputable def mixedVectorCascade (n : ℕ) (mode : ℕ → Section5GaussianMode)
    (m v : ℕ → ℝ) (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    ℕ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0 => F
  | j+1 => match mode j with
    | .independent => AT.gtVectorStep n (m j) (Real.sqrt (v j)) 0
        (AT.gtVectorStep n (m j) 0 (Real.sqrt (v j)) (mixedVectorCascade n mode m v F j))
    | .shared => AT.gtVectorStep n (m j) (Real.sqrt (v j)) (Real.sqrt (v j))
        (mixedVectorCascade n mode m v F j)
    | .opposite => AT.gtVectorStep n (m j) (Real.sqrt (v j)) (-Real.sqrt (v j))
        (mixedVectorCascade n mode m v F j)

variable [TopologicalSpace P] [FirstCountableTopology P]

theorem mixedScalarCascade_good (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) (j : ℕ) :
    GTFrame.GoodFam (mixedScalarCascade mode m v j) (mixedScalarCascadeD mode m v j) := by
  induction j with
  | zero =>
    simpa only [mixedScalarCascade, mixedScalarCascadeD, coupledSite_eq_gtTerminal,
      GTFrame.fLbase] using (GTFrame.goodFam_fLbase (P := P))
  | succ j ih =>
    simp only [mixedScalarCascade, mixedScalarCascadeD]
    cases mode j with
    | independent =>
      exact finiteStep_good
        (finiteStep_good ih (hm j) continuous_const (hv j).sqrt)
        (hm j) (hv j).sqrt continuous_const
    | shared => exact finiteStep_good ih (hm j) (hv j).sqrt (hv j).sqrt
    | opposite => exact finiteStep_good ih (hm j) (hv j).sqrt (hv j).sqrt.neg

theorem mixedVectorCascade_eq_sum (n : ℕ) (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) (j : ℕ) (p : P) (l : ℝ) (x y : Fin n → ℝ) :
    mixedVectorCascade n mode m (fun j => v j p)
      (fun x y => ∑ i, coupledSite l (x i) (y i)) j x y =
      ∑ i, mixedScalarCascade mode m v j p l (x i,y i) := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    have he := funext fun x => funext (ih x)
    have hg := mixedScalarCascade_good mode m v hm hv j
    simp only [mixedVectorCascade, mixedScalarCascade]
    rw [he]
    cases mode j with
    | independent =>
      have hi := fun x y => gtVectorStep_sum_good hg n (hm j)
        (fun _ => 0) (fun p => Real.sqrt (v j p)) p l x y
      rw [show AT.gtVectorStep n (m j) 0 (Real.sqrt (v j p))
        (fun x y => ∑ i, mixedScalarCascade mode m v j p l (x i,y i)) = _
        from funext fun x => funext (hi x)]
      exact gtVectorStep_sum_good (finiteStep_good hg (hm j) continuous_const (hv j).sqrt)
        n (hm j) (fun p => Real.sqrt (v j p)) (fun _ => 0) p l x y
    | shared =>
      exact gtVectorStep_sum_good hg n (hm j)
        (fun p => Real.sqrt (v j p)) (fun p => Real.sqrt (v j p)) p l x y
    | opposite =>
      exact gtVectorStep_sum_good hg n (hm j)
        (fun p => Real.sqrt (v j p)) (fun p => -Real.sqrt (v j p)) p l x y

omit [FirstCountableTopology P] in
private theorem goodFam_one_growth {F D : P → ℝ → ℝ × ℝ → ℝ}
    (h : GTFrame.GoodFam F D) (p : P) (l : ℝ) :
    CoupledGrowth (fun x y : Fin 1 → ℝ => F p l (x 0,y 0)) := by
  refine ⟨(h.contF_pt p l).measurable.comp (by fun_prop), |F p l (0,0)|, 1,
    zero_le_one, fun x y => ?_⟩
  have H := h.lipx p l (x 0,y 0) (0,0)
  have H' := abs_sub_abs_le_abs_sub (F p l (x 0,y 0)) (F p l (0,0))
  simp only [sub_zero, l1, Fin.sum_univ_one, one_mul] at H ⊢
  linarith

omit [FirstCountableTopology P] in
private theorem goodFam_shift_growth {F D : P → ℝ → ℝ × ℝ → ℝ}
    (h : GTFrame.GoodFam F D) (p : P) (l a b x y : ℝ) :
    HasLinearGrowth (fun z => F p l (x+a*z,y+b*z)) :=
  ⟨|F p l (x,y)|, |a|+|b|, abs_nonneg _, add_nonneg (abs_nonneg _) (abs_nonneg _),
    h.bound_shift p l a b (x,y)⟩

omit [TopologicalSpace P] [FirstCountableTopology P] in
theorem finiteStep_eq_gtScalarStep (m : ℝ) (a b : P → ℝ)
    (F : P → ℝ → ℝ × ℝ → ℝ) (p : P) (l x y : ℝ) :
    GTFrame.finiteStep (gaussianReal 0 1) m a b F p l (x,y) =
      AT.gtScalarStep m (a p) (b p) (fun x y => F p l (x,y)) x y := by
  simp only [GTFrame.finiteStep, AT.gtScalarStep]
  split_ifs <;> rfl

private theorem independent_finiteSteps_eq {F D : P → ℝ → ℝ × ℝ → ℝ}
    (h : GTFrame.GoodFam F D) {m : ℝ} (hm : 0≤m)
    {v : P → ℝ} (hv : Continuous v) (p : P) (l x y : ℝ) :
    GTFrame.finiteStep (gaussianReal 0 1) m (fun p => Real.sqrt (v p)) (fun _ => 0)
      (GTFrame.finiteStep (gaussianReal 0 1) m (fun _ => 0) (fun p => Real.sqrt (v p)) F)
        p l (x,y) =
    independentStepPi 1 m (v p) (fun x y => F p l (x 0,y 0)) (fun _ => x) (fun _ => y) := by
  rw [independentStepPi_eq_gtVectorSteps m (v p) (goodFam_one_growth h p l)]
  have hi := fun x y => gtVectorStep_sum_good h 1 hm
    (fun _ => 0) (fun p => Real.sqrt (v p)) p l x y
  simp only [Fin.sum_univ_one] at hi
  rw [show AT.gtVectorStep 1 m 0 (Real.sqrt (v p)) (fun x y => F p l (x 0,y 0)) = _
    from funext fun x => funext (hi x)]
  have ho := gtVectorStep_sum_good (finiteStep_good h hm (a := fun _ : P => 0) continuous_const hv.sqrt)
    1 hm (fun p => Real.sqrt (v p)) (fun _ => 0) p l (fun _ => x) (fun _ => y)
  simpa only [Fin.sum_univ_one] using ho.symm

/-- Proposition 5.11's non-strict comparison for an arbitrary finite ordering
of all three Gaussian modes. Mass zero and variance zero are both allowed. -/
theorem mixedScalarCascade_zero_le (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) (j : ℕ) (p : P) (x y : ℝ) :
    mixedScalarCascade mode m v j p 0 (x,y) ≤
      scalarFieldCascade (fun i => (mode i).scalarMass (m i)) (fun i => v i p) j x+
      scalarFieldCascade (fun i => (mode i).scalarMass (m i)) (fun i => v i p) j y := by
  induction j generalizing x y with
  | zero => exact (coupledSite_zero x y).le
  | succ j ih =>
    have hg := mixedScalarCascade_good mode m v hm hv j
    have hS := scalarFieldCascade_props (fun i => (mode i).scalarMass (m i)) (fun i => v i p) j
    simp only [mixedScalarCascade, scalarFieldCascade]
    cases hmode : mode j with
    | independent =>
      simp only [Section5GaussianMode.scalarMass]
      rw [independent_finiteSteps_eq hg (hm j) (hv j)]
      exact independentStepPi_one_le_scalar (hm j) (goodFam_one_growth hg p 0)
        hS.2.1 hS.1 ih x y
    | shared =>
      simp only [Section5GaussianMode.scalarMass]
      rw [finiteStep_eq_gtScalarStep]
      exact gtScalarStep_shared_le (hm j) (goodFam_shift_growth hg p 0 _ _ x y)
        (hg.cont_shift p 0 _ _ (x,y)).measurable hS.2.1 hS.1 ih
    | opposite =>
      simp only [Section5GaussianMode.scalarMass]
      rw [finiteStep_eq_gtScalarStep]
      exact gtScalarStep_opposite_le (hm j) (goodFam_shift_growth hg p 0 _ _ x y)
        (hg.cont_shift p 0 _ _ (x,y)).measurable hS.2.1 hS.1 ih

omit [FirstCountableTopology P] in
private theorem scalar_sum_good {G : ℝ → ℝ}
    (hL : ∀ x y, |G x-G y|≤|x-y|) :
    GTFrame.GoodFam (fun (_ : P) (_ : ℝ) (z : ℝ × ℝ) => G z.1+G z.2)
      (fun _ _ _ => 0) := by
  have hc : Continuous G := (show LipschitzWith 1 G from
    LipschitzWith.of_dist_le_mul (fun x y => by simpa [Real.dist_eq] using hL x y)).continuous
  refine ⟨?_, continuous_const, fun p l z => hasDerivAt_const l _, ?_, by simp⟩
  · exact (hc.comp (continuous_snd.comp continuous_snd).fst).add
      (hc.comp (continuous_snd.comp continuous_snd).snd)
  · intro p l x y
    have he : G x.1+G x.2-(G y.1+G y.2)=(G x.1-G y.1)+(G x.2-G y.2) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (hL _ _) (hL _ _))

omit [FirstCountableTopology P] in
private theorem rankOne_step_lt_scalar_of_ae {F D : P → ℝ → ℝ × ℝ → ℝ}
    (hF : GTFrame.GoodFam F D) {G : ℝ → ℝ}
    (hG : HasLinearGrowth G) (hGm : Measurable G) (hGL : ∀ x y, |G x-G y|≤|x-y|)
    {m v b : ℝ} (hm : 0≤m) (hb : b=Real.sqrt v ∨ b= -Real.sqrt v)
    (p : P) (x y : ℝ)
    (h : ∀ᵐ z ∂gaussianReal 0 1,
      F p 0 (x+Real.sqrt v*z,y+b*z)<G (x+Real.sqrt v*z)+G (y+b*z)) :
    AT.gtScalarStep m (Real.sqrt v) b (fun x y => F p 0 (x,y)) x y <
      parisiStep (2*m) v G x+parisiStep (2*m) v G y := by
  have hS := scalar_sum_good (P := P) hGL
  apply (gtScalarStep_lt_of_ae_lt (E := fun x y => G x+G y) hm (goodFam_shift_growth hF p 0 _ _ x y)
    (hF.cont_shift p 0 _ _ (x,y)).measurable (goodFam_shift_growth hS p 0 _ _ x y)
    (hS.cont_shift p 0 _ _ (x,y)).measurable h).trans_le
  rcases hb with rfl | rfl
  · exact gtScalarStep_shared_le hm (goodFam_shift_growth hS p 0 _ _ x y)
      (hS.cont_shift p 0 _ _ (x,y)).measurable hG hGm (fun _ _ => le_rfl)
  · exact gtScalarStep_opposite_le hm (goodFam_shift_growth hS p 0 _ _ x y)
      (hS.cont_shift p 0 _ _ (x,y)).measurable hG hGm (fun _ _ => le_rfl)

private theorem gaussian_ae_shift_ne {x y : ℝ} (hxy : x≠y) (a b : ℝ) :
    ∀ᵐ z ∂gaussianReal 0 1, x+a*z≠y+b*z := by
  by_cases hab : a=b
  · exact Eventually.of_forall (fun z he => hxy (by rw [hab] at he; linarith))
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [(gaussianReal 0 1).ae_ne ((y-x)/(a-b))] with z hz
  intro he
  apply hz
  apply (eq_div_iff (sub_ne_zero.mpr hab)).2
  linarith

private theorem gaussian_ae_off_diagonals {x y : ℝ} (hxy : x≠y) (hxy' : x≠-y) (a b : ℝ) :
    ∀ᵐ z ∂gaussianReal 0 1, x+a*z≠y+b*z ∧ x+a*z≠-(y+b*z) := by
  filter_upwards [gaussian_ae_shift_ne hxy a b, gaussian_ae_shift_ne hxy' a (-b)] with z h₁ h₂
  exact ⟨h₁, fun he => h₂ (by linarith)⟩

/-- The scalar reference is exactly the recursion with doubled shared masses. -/
noncomputable abbrev mixedScalarReference (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (j : ℕ) (p : P) : ℝ → ℝ :=
  scalarFieldCascade (fun i => (mode i).scalarMass (m i)) (fun i => v i p) j

/-- Once strictness holds everywhere, every additional genuine Gaussian mode
preserves it. All masses and variances may vanish. -/
theorem mixedScalarCascade_strict_succ (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) (j : ℕ) (p : P)
    (hstrict : ∀ x y, mixedScalarCascade mode m v j p 0 (x,y)<
      mixedScalarReference mode m v j p x+mixedScalarReference mode m v j p y)
    (x y : ℝ) : mixedScalarCascade mode m v (j+1) p 0 (x,y)<
      mixedScalarReference mode m v (j+1) p x+mixedScalarReference mode m v (j+1) p y := by
  have hg := mixedScalarCascade_good mode m v hm hv j
  have hS := scalarFieldCascade_props (fun i => (mode i).scalarMass (m i)) (fun i => v i p) j
  have hSg := scalar_sum_good (P := P) hS.2.2
  simp only [mixedScalarCascade, mixedScalarReference, scalarFieldCascade]
  cases mode j with
  | independent =>
    simp only [Section5GaussianMode.scalarMass]
    rw [independent_finiteSteps_eq hg (hm j) (hv j)]
    have H := independentStepPi_lt_of_ae_lt (v := v j p) (hm j) (goodFam_one_growth hg p 0)
      (goodFam_one_growth hSg p 0) (fun _ => x) (fun _ => y)
      (Eventually.of_forall (fun z => hstrict _ _))
    have Hle := independentStepPi_one_le_scalar (v := v j p) (hm j) (goodFam_one_growth hSg p 0)
      hS.2.1 hS.1 (fun _ _ => le_rfl) x y
    exact H.trans_le Hle
  | shared =>
    simp only [Section5GaussianMode.scalarMass]
    rw [finiteStep_eq_gtScalarStep]
    exact rankOne_step_lt_scalar_of_ae hg hS.2.1 hS.1 hS.2.2 (hm j) (Or.inl rfl) p x y
      (Eventually.of_forall (fun z => hstrict _ _))
  | opposite =>
    simp only [Section5GaussianMode.scalarMass]
    rw [finiteStep_eq_gtScalarStep]
    exact rankOne_step_lt_scalar_of_ae hg hS.2.1 hS.1 hS.2.2 (hm j) (Or.inr rfl) p x y
      (Eventually.of_forall (fun z => hstrict _ _))

/-- A positive independent variance spreads the off-two-diagonals strict
comparison to all starting pairs, regardless of its mass. -/
theorem mixedScalarCascade_strict_independent_succ (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) (j : ℕ) (p : P)
    (hmode : mode j=.independent) (hvp : 0<v j p)
    (hstrict : ∀ x y, x≠y → x≠-y → mixedScalarCascade mode m v j p 0 (x,y)<
      mixedScalarReference mode m v j p x+mixedScalarReference mode m v j p y)
    (x y : ℝ) : mixedScalarCascade mode m v (j+1) p 0 (x,y)<
      mixedScalarReference mode m v (j+1) p x+mixedScalarReference mode m v (j+1) p y := by
  have hg := mixedScalarCascade_good mode m v hm hv j
  have hS := scalarFieldCascade_props (fun i => (mode i).scalarMass (m i)) (fun i => v i p) j
  simp only [mixedScalarCascade, mixedScalarReference, scalarFieldCascade, hmode,
    Section5GaussianMode.scalarMass]
  rw [independent_finiteSteps_eq hg (hm j) (hv j)]
  exact independentStepPi_one_lt_scalar_of_off_diagonals (hm j) hvp (goodFam_one_growth hg p 0)
    hS.2.1 hS.1 hstrict x y

/-- Strict comparison away from both exceptional lines survives arbitrary
intervening modes, including zero variances. -/
theorem mixedScalarCascade_strictOff_succ (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) (j : ℕ) (p : P)
    (hstrict : ∀ x y, x≠y → x≠-y → mixedScalarCascade mode m v j p 0 (x,y)<
      mixedScalarReference mode m v j p x+mixedScalarReference mode m v j p y)
    (x y : ℝ) (hxy : x≠y) (hxy' : x≠-y) : mixedScalarCascade mode m v (j+1) p 0 (x,y)<
      mixedScalarReference mode m v (j+1) p x+mixedScalarReference mode m v (j+1) p y := by
  have hg := mixedScalarCascade_good mode m v hm hv j
  have hS := scalarFieldCascade_props (fun i => (mode i).scalarMass (m i)) (fun i => v i p) j
  have hSg := scalar_sum_good (P := P) hS.2.2
  cases he : mode j with
  | independent =>
    by_cases hvp : 0<v j p
    · exact mixedScalarCascade_strict_independent_succ mode m v hm hv j p he hvp hstrict x y
    have hzero : Real.sqrt (v j p)=0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hvp)
    simp only [mixedScalarCascade, mixedScalarReference, scalarFieldCascade, he,
      Section5GaussianMode.scalarMass]
    rw [independent_finiteSteps_eq hg (hm j) (hv j)]
    have H := independentStepPi_lt_of_ae_lt (v := v j p) (hm j) (goodFam_one_growth hg p 0)
      (goodFam_one_growth hSg p 0) (fun _ => x) (fun _ => y)
      (Eventually.of_forall (fun z => by
        simpa only [hzero, zero_mul, add_zero] using hstrict x y hxy hxy'))
    exact H.trans_le (independentStepPi_one_le_scalar (v := v j p) (hm j)
      (goodFam_one_growth hSg p 0) hS.2.1 hS.1 (fun _ _ => le_rfl) x y)
  | shared =>
    simp only [mixedScalarCascade, mixedScalarReference, scalarFieldCascade, he,
      Section5GaussianMode.scalarMass]
    rw [finiteStep_eq_gtScalarStep]
    exact rankOne_step_lt_scalar_of_ae hg hS.2.1 hS.1 hS.2.2 (hm j) (Or.inl rfl) p x y
      ((gaussian_ae_off_diagonals hxy hxy' _ _).mono fun z hz => hstrict _ _ hz.1 hz.2)
  | opposite =>
    simp only [mixedScalarCascade, mixedScalarReference, scalarFieldCascade, he,
      Section5GaussianMode.scalarMass]
    rw [finiteStep_eq_gtScalarStep]
    exact rankOne_step_lt_scalar_of_ae hg hS.2.1 hS.1 hS.2.2 (hm j) (Or.inr rfl) p x y
      ((gaussian_ae_off_diagonals hxy hxy' _ _).mono fun z hz => hstrict _ _ hz.1 hz.2)

/-- Positive shared mass and variance create genuine strictness from the
actual scalar Hessian, without any strictness assumption on earlier levels. -/
theorem mixedScalarCascade_strict_shared_succ (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) (hscalar : ∀ j, (mode j).scalarMass (m j)∈Set.Icc 0 1)
    (j : ℕ) (p : P) (hmode : mode j≠.independent) (hmp : 0<m j) (hvp : 0<v j p)
    (x y : ℝ) (hxy : x≠y) (hxy' : x≠-y) : mixedScalarCascade mode m v (j+1) p 0 (x,y)<
      mixedScalarReference mode m v (j+1) p x+mixedScalarReference mode m v (j+1) p y := by
  have hg := mixedScalarCascade_good mode m v hm hv j
  have hS := scalarFieldCascade_props (fun i => (mode i).scalarMass (m i)) (fun i => v i p) j
  have hC := scalarFieldCascade_C2_pos (fun i => (mode i).scalarMass (m i)) (fun i => v i p) hscalar j
  have hSM := strictMono_scalarFieldCascadeSlope (fun i => (mode i).scalarMass (m i))
    (fun i => v i p) hscalar j
  have hle := mixedScalarCascade_zero_le mode m v hm hv j p
  simp only [mixedScalarCascade, mixedScalarReference, scalarFieldCascade]
  cases he : mode j with
  | independent => exact False.elim (hmode he)
  | shared =>
    simp only [Section5GaussianMode.scalarMass]
    rw [finiteStep_eq_gtScalarStep]
    exact gtScalarStep_shared_lt_of_strictMono_deriv hmp hvp
      (goodFam_shift_growth hg p 0 _ _ x y) (hg.cont_shift p 0 _ _ (x,y)).measurable
      hS.2.1 hC.1.1 hSM hle hxy
  | opposite =>
    simp only [Section5GaussianMode.scalarMass]
    rw [finiteStep_eq_gtScalarStep]
    exact gtScalarStep_opposite_lt_of_strictMono_deriv hmp hvp
      (goodFam_shift_growth hg p 0 _ _ x y) (hg.cont_shift p 0 _ _ (x,y)).measurable
      hS.2.1 hC.1.1 hSM (scalarFieldCascade_even _ _ _) hle hxy'

theorem mixedScalarCascade_strict_mono (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) {a b : ℕ} (hab : a≤b) (p : P)
    (hstrict : ∀ x y, mixedScalarCascade mode m v a p 0 (x,y)<
      mixedScalarReference mode m v a p x+mixedScalarReference mode m v a p y) :
    ∀ x y, mixedScalarCascade mode m v b p 0 (x,y)<
      mixedScalarReference mode m v b p x+mixedScalarReference mode m v b p y := by
  induction b, hab using Nat.le_induction with
  | base => exact hstrict
  | succ b hb ih => exact mixedScalarCascade_strict_succ mode m v hm hv b p ih

theorem mixedScalarCascade_strictOff_mono (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) {a b : ℕ} (hab : a≤b) (p : P)
    (hstrict : ∀ x y, x≠y → x≠-y → mixedScalarCascade mode m v a p 0 (x,y)<
      mixedScalarReference mode m v a p x+mixedScalarReference mode m v a p y) :
    ∀ x y, x≠y → x≠-y → mixedScalarCascade mode m v b p 0 (x,y)<
      mixedScalarReference mode m v b p x+mixedScalarReference mode m v b p y := by
  induction b, hab using Nat.le_induction with
  | base => exact hstrict
  | succ b hb ih => exact mixedScalarCascade_strictOff_succ mode m v hm hv b p ih

/-- The strict ordering obstruction in Proposition 5.11: in integration
order, an active shared step followed by an active independent step forces a
strict final comparison. No assumptions on intervening modes are added. -/
theorem mixedScalarCascade_lt_of_shared_before_independent
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (hm : ∀ j, 0≤m j) (hv : ∀ j, Continuous (v j))
    (hscalar : ∀ j, (mode j).scalarMass (m j)∈Set.Icc 0 1)
    {c b j : ℕ} (hcb : c<b) (hbj : b<j) (p : P)
    (hc : mode c≠.independent) (hmc : 0<m c) (hvc : 0<v c p)
    (hb : mode b=.independent) (hvb : 0<v b p) (x y : ℝ) :
    mixedScalarCascade mode m v j p 0 (x,y)<
      mixedScalarReference mode m v j p x+mixedScalarReference mode m v j p y := by
  have hcstrict := mixedScalarCascade_strict_shared_succ mode m v hm hv hscalar c p hc hmc hvc
  have hbstrict := mixedScalarCascade_strictOff_mono mode m v hm hv (by omega : c+1≤b) p hcstrict
  have hspread := mixedScalarCascade_strict_independent_succ mode m v hm hv b p hb hvb hbstrict
  exact mixedScalarCascade_strict_mono mode m v hm hv (by omega : b+1≤j) p hspread x y

/-- Equality enforces Talagrand's order condition (5.44), written in the
bottom-up integration indexing of this module. -/
theorem mixedScalarCascade_eq_implies_order (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) (hscalar : ∀ j, (mode j).scalarMass (m j)∈Set.Icc 0 1)
    (j : ℕ) (p : P) (h : ℝ)
    (heq : mixedScalarCascade mode m v j p 0 (h,h)=2*mixedScalarReference mode m v j p h)
    {b c : ℕ} (hbj : b<j) (_hcj : c<j)
    (hb : mode b=.independent) (hvb : 0<v b p)
    (hc : mode c≠.independent) (hmc : 0<m c) (hvc : 0<v c p) : b<c := by
  by_contra hbc
  have hne : b≠c := fun he => hc (he ▸ hb)
  have H := mixedScalarCascade_lt_of_shared_before_independent mode m v hm hv hscalar
    (by omega : c<b) hbj p hc hmc hvc hb hvb h h
  rw [heq] at H
  linarith

/-- An opposite step creates strictness everywhere off the anti-diagonal. -/
theorem mixedScalarCascade_strict_opposite_succ (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) (hscalar : ∀ j, (mode j).scalarMass (m j)∈Set.Icc 0 1)
    (j : ℕ) (p : P) (hmode : mode j=.opposite) (hmp : 0<m j) (hvp : 0<v j p)
    (x y : ℝ) (hxy : x≠-y) : mixedScalarCascade mode m v (j+1) p 0 (x,y)<
      mixedScalarReference mode m v (j+1) p x+mixedScalarReference mode m v (j+1) p y := by
  have hg := mixedScalarCascade_good mode m v hm hv j
  have hS := scalarFieldCascade_props (fun i => (mode i).scalarMass (m i)) (fun i => v i p) j
  have hC := scalarFieldCascade_C2_pos (fun i => (mode i).scalarMass (m i)) (fun i => v i p) hscalar j
  simp only [mixedScalarCascade, mixedScalarReference, scalarFieldCascade, hmode,
    Section5GaussianMode.scalarMass]
  rw [finiteStep_eq_gtScalarStep]
  exact gtScalarStep_opposite_lt_of_strictMono_deriv hmp hvp
    (goodFam_shift_growth hg p 0 _ _ x y) (hg.cont_shift p 0 _ _ (x,y)).measurable
    hS.2.1 hC.1.1 (strictMono_scalarFieldCascadeSlope _ _ hscalar j)
    (scalarFieldCascade_even _ _ _) (mixedScalarCascade_zero_le mode m v hm hv j p) hxy

private theorem gaussian_ae_shift_ne_of_slope_ne (x y : ℝ) {a b : ℝ} (hab : a≠b) :
    ∀ᵐ z ∂gaussianReal 0 1, x+a*z≠y+b*z := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [(gaussianReal 0 1).ae_ne ((y-x)/(a-b))] with z hz
  intro he
  apply hz
  apply (eq_div_iff (sub_ne_zero.mpr hab)).2
  linarith

/-- A positive ordinary shared Gaussian spreads anti-diagonal strictness to
all points. Its mass may be zero, as for the outer frozen field. -/
theorem mixedScalarCascade_strict_shared_of_anti_succ (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) (j : ℕ) (p : P)
    (hmode : mode j=.shared) (hvp : 0<v j p)
    (hstrict : ∀ x y, x≠-y → mixedScalarCascade mode m v j p 0 (x,y)<
      mixedScalarReference mode m v j p x+mixedScalarReference mode m v j p y)
    (x y : ℝ) : mixedScalarCascade mode m v (j+1) p 0 (x,y)<
      mixedScalarReference mode m v (j+1) p x+mixedScalarReference mode m v (j+1) p y := by
  have hg := mixedScalarCascade_good mode m v hm hv j
  have hS := scalarFieldCascade_props (fun i => (mode i).scalarMass (m i)) (fun i => v i p) j
  simp only [mixedScalarCascade, mixedScalarReference, scalarFieldCascade, hmode,
    Section5GaussianMode.scalarMass]
  rw [finiteStep_eq_gtScalarStep]
  apply rankOne_step_lt_scalar_of_ae hg hS.2.1 hS.1 hS.2.2 (hm j) (Or.inl rfl) p x y
  have H := gaussian_ae_shift_ne_of_slope_ne x (-y)
    (show Real.sqrt (v j p)≠-Real.sqrt (v j p) by linarith [Real.sqrt_pos.2 hvp])
  filter_upwards [H] with z hz
  exact hstrict _ _ (fun he => hz (by linarith))

/-- Anti-diagonal strictness is retained through any intervening mode. -/
theorem mixedScalarCascade_strictAnti_succ (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) (j : ℕ) (p : P)
    (hstrict : ∀ x y, x≠-y → mixedScalarCascade mode m v j p 0 (x,y)<
      mixedScalarReference mode m v j p x+mixedScalarReference mode m v j p y)
    (x y : ℝ) (hxy : x≠-y) : mixedScalarCascade mode m v (j+1) p 0 (x,y)<
      mixedScalarReference mode m v (j+1) p x+mixedScalarReference mode m v (j+1) p y := by
  have hg := mixedScalarCascade_good mode m v hm hv j
  have hS := scalarFieldCascade_props (fun i => (mode i).scalarMass (m i)) (fun i => v i p) j
  have hSg := scalar_sum_good (P := P) hS.2.2
  cases he : mode j with
  | independent =>
    by_cases hvp : 0<v j p
    · exact mixedScalarCascade_strict_independent_succ mode m v hm hv j p he hvp
        (fun x y _ hxy => hstrict x y hxy) x y
    have hzero : Real.sqrt (v j p)=0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hvp)
    simp only [mixedScalarCascade, mixedScalarReference, scalarFieldCascade, he,
      Section5GaussianMode.scalarMass]
    rw [independent_finiteSteps_eq hg (hm j) (hv j)]
    have H := independentStepPi_lt_of_ae_lt (v := v j p) (hm j) (goodFam_one_growth hg p 0)
      (goodFam_one_growth hSg p 0) (fun _ => x) (fun _ => y)
      (Eventually.of_forall (fun z => by
        simpa only [hzero, zero_mul, add_zero] using hstrict x y hxy))
    exact H.trans_le (independentStepPi_one_le_scalar (v := v j p) (hm j)
      (goodFam_one_growth hSg p 0) hS.2.1 hS.1 (fun _ _ => le_rfl) x y)
  | shared =>
    by_cases hvp : 0<v j p
    · exact mixedScalarCascade_strict_shared_of_anti_succ mode m v hm hv j p he hvp hstrict x y
    have hzero : Real.sqrt (v j p)=0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hvp)
    simp only [mixedScalarCascade, mixedScalarReference, scalarFieldCascade, he,
      Section5GaussianMode.scalarMass]
    rw [finiteStep_eq_gtScalarStep]
    exact rankOne_step_lt_scalar_of_ae hg hS.2.1 hS.1 hS.2.2 (hm j) (Or.inl rfl) p x y
      (Eventually.of_forall (fun z => by
        simpa only [hzero, zero_mul, add_zero] using hstrict x y hxy))
  | opposite =>
    simp only [mixedScalarCascade, mixedScalarReference, scalarFieldCascade, he,
      Section5GaussianMode.scalarMass]
    rw [finiteStep_eq_gtScalarStep]
    exact rankOne_step_lt_scalar_of_ae hg hS.2.1 hS.1 hS.2.2 (hm j) (Or.inr rfl) p x y
      (Eventually.of_forall (fun z => hstrict _ _ (fun he => hxy (by linarith))))

theorem mixedScalarCascade_strictAnti_mono (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0≤m j)
    (hv : ∀ j, Continuous (v j)) {a b : ℕ} (hab : a≤b) (p : P)
    (hstrict : ∀ x y, x≠-y → mixedScalarCascade mode m v a p 0 (x,y)<
      mixedScalarReference mode m v a p x+mixedScalarReference mode m v a p y) :
    ∀ x y, x≠-y → mixedScalarCascade mode m v b p 0 (x,y)<
      mixedScalarReference mode m v b p x+mixedScalarReference mode m v b p y := by
  induction b, hab using Nat.le_induction with
  | base => exact hstrict
  | succ b hb ih => exact mixedScalarCascade_strictAnti_succ mode m v hm hv b p ih

/-- The negative-case mechanism in Proposition 5.11: a positive opposite
step, followed outwards by a positive ordinary shared variance, produces a
strict final comparison. Existence of these active tagged steps is separate. -/
theorem mixedScalarCascade_lt_of_opposite_before_shared
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (hm : ∀ j, 0≤m j) (hv : ∀ j, Continuous (v j))
    (hscalar : ∀ j, (mode j).scalarMass (m j)∈Set.Icc 0 1)
    {c b j : ℕ} (hcb : c<b) (hbj : b<j) (p : P)
    (hc : mode c=.opposite) (hmc : 0<m c) (hvc : 0<v c p)
    (hb : mode b=.shared) (hvb : 0<v b p) (x y : ℝ) :
    mixedScalarCascade mode m v j p 0 (x,y)<
      mixedScalarReference mode m v j p x+mixedScalarReference mode m v j p y := by
  have hcstrict := mixedScalarCascade_strict_opposite_succ mode m v hm hv hscalar c p hc hmc hvc
  have hbstrict := mixedScalarCascade_strictAnti_mono mode m v hm hv (by omega : c+1≤b) p hcstrict
  have hspread := mixedScalarCascade_strict_shared_of_anti_succ mode m v hm hv b p hb hvb hbstrict
  exact mixedScalarCascade_strict_mono mode m v hm hv (by omega : b+1≤j) p hspread x y

end SpinGlass.Targets
