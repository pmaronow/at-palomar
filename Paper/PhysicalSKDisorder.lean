module

public import Paper.PhysicalSKBridge
public import Lemmas.Gaussian.CanonicalModel
public import Lemmas.SmartPath.IndependentEndpoint
public import Lemmas.AT.Definitions

@[expose] public section

/-! # A concrete exact-covariance Gaussian smart-path model for the paper -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Paper

/-- A single probability space carries the couplings and fields for every system size. -/
abbrev PhysicalSKGaussianSpace := ((ℕ × ℕ) ⊕ ℕ) → ℝ

noncomputable def physicalSKGaussianMeasure : Measure PhysicalSKGaussianSpace :=
  Measure.infinitePi (fun _ : (ℕ × ℕ) ⊕ ℕ => gaussianReal 0 1)

noncomputable instance : MeasureSpace PhysicalSKGaussianSpace := ⟨physicalSKGaussianMeasure⟩

instance physicalSKGaussian_probability :
    IsProbabilityMeasure (volume : Measure PhysicalSKGaussianSpace) := by
  change IsProbabilityMeasure physicalSKGaussianMeasure
  unfold physicalSKGaussianMeasure
  infer_instance

private theorem physicalCoordinates_independent :
    iIndepFun (fun k : (ℕ × ℕ) ⊕ ℕ => fun ω : PhysicalSKGaussianSpace => ω k)
      (volume : Measure PhysicalSKGaussianSpace) := by
  exact iIndepFun_infinitePi (X := fun _ x => x) (by fun_prop)

theorem physicalCoordinate_law (k : (ℕ × ℕ) ⊕ ℕ) :
    (volume : Measure PhysicalSKGaussianSpace).map (fun ω => ω k) = gaussianReal 0 1 :=
  (measurePreserving_eval_infinitePi (fun _ : (ℕ × ℕ) ⊕ ℕ => gaussianReal 0 1) k).map_eq

/-- Increasing pairs occupy off-diagonal coordinates; `(0,0)` supplies the common noise. -/
def physicalSKCoordinateIndex {n : ℕ} : Option (SKEdge n) → (ℕ × ℕ)
  | none => (0, 0)
  | some e => (e.val.1.val, e.val.2.val)

private theorem physicalSKCoordinateIndex_injective (n : ℕ) :
    Function.Injective (physicalSKCoordinateIndex (n := n)) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some e =>
      have he := e.property
      simp only [physicalSKCoordinateIndex, Prod.mk.injEq] at hab
      have hv : e.val.1.val < e.val.2.val := he
      omega
  | some e =>
    cases b with
    | none =>
      have he := e.property
      simp only [physicalSKCoordinateIndex, Prod.mk.injEq] at hab
      have hv : e.val.1.val < e.val.2.val := he
      omega
    | some f =>
      apply congrArg some
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · exact (Prod.mk.inj hab).1
      · exact (Prod.mk.inj hab).2

noncomputable def physicalSKCoordinates (n : ℕ) (ω : PhysicalSKGaussianSpace)
    (k : Option (SKEdge n)) : ℝ := ω (Sum.inl (physicalSKCoordinateIndex k))

noncomputable def physicalFieldCoordinates (n : ℕ) (ω : PhysicalSKGaussianSpace)
    (i : Fin n) : ℝ := ω (Sum.inr i.val)

theorem physicalSKCoordinates_independent (n : ℕ) :
    iIndepFun (fun k => fun ω => physicalSKCoordinates n ω k)
      (volume : Measure PhysicalSKGaussianSpace) := by
  exact physicalCoordinates_independent.precomp
    (Sum.inl_injective.comp (physicalSKCoordinateIndex_injective n))

theorem physicalFieldCoordinates_independent (n : ℕ) :
    iIndepFun (fun i : Fin n => fun ω => physicalFieldCoordinates n ω i)
      (volume : Measure PhysicalSKGaussianSpace) := by
  exact physicalCoordinates_independent.precomp (Sum.inr_injective.comp Fin.val_injective)

private theorem physicalSKCoordinates_law (n : ℕ) :
    (volume : Measure PhysicalSKGaussianSpace).map (physicalSKCoordinates n) =
      Measure.pi (fun _ : Option (SKEdge n) => gaussianReal 0 1) := by
  change (volume : Measure PhysicalSKGaussianSpace).map
    (fun ω i => ω (Sum.inl (physicalSKCoordinateIndex i))) = _
  have hm := (physicalSKCoordinates_independent n).map_fun_eq_pi_map
    (fun k => (measurable_pi_apply _).aemeasurable)
  simpa only [physicalCoordinate_law] using hm

/-- Linear energy vectors from arbitrary finite coefficient arrays. -/
noncomputable def gaussianEnergyLinearMap (n : ℕ) {I : Type*} [Fintype I]
    (a : SKConfiguration n → I → ℝ) : (I → ℝ) →L[ℝ] SpinGlass.EnergySpace n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun σ => ∑ i, a σ i * x i)
      map_add' := by
        intro x y
        ext σ
        change (∑ i, a σ i * (x i + y i)) =
          (∑ i, a σ i * x i) + ∑ i, a σ i * y i
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        ext σ
        change (∑ i, a σ i * (c * x i)) = c * ∑ i, a σ i * x i
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring }

noncomputable def gaussianCoordinateEnergy {Ω I : Type*} [Fintype I] (n : ℕ)
    (X : I → Ω → ℝ) (a : SKConfiguration n → I → ℝ) (ω : Ω) : SpinGlass.EnergySpace n :=
  gaussianEnergyLinearMap n a (fun i => X i ω)

noncomputable def gaussianCoordinateEnergy_gaussian {Ω I : Type*}
    [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)] [Fintype I]
    (n : ℕ) (X : I → Ω → ℝ) (a : SKConfiguration n → I → ℝ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, (volume : Measure Ω).map (X i) = gaussianReal 0 1)
    (hI : iIndepFun X (volume : Measure Ω)) :
    PhysLean.Probability.GaussianIBP.IsGaussianHilbert (gaussianCoordinateEnergy n X a) := by
  let Y : Ω → (I → ℝ) := fun ω i => X i ω
  have hYm : Measurable Y := measurable_pi_iff.mpr hXm
  have hYg : HasGaussianLaw Y (volume : Measure Ω) :=
    hI.hasGaussianLaw fun i => standardGaussianCoordinate_gaussian _ _ (hXm i) (hX i)
  have hY0 : (∫ ω, Y ω ∂(volume : Measure Ω)) = 0 := by
    ext i
    rw [eval_integral (fun j => hYg.integrable.eval j)]
    exact standardGaussianCoordinate_mean _ _ (hXm i) (hX i)
  apply PhysLean.Probability.GaussianIBP.IsGaussianHilbert.of_hasGaussianLaw
      (gaussianCoordinateEnergy n X a)
  · exact (gaussianEnergyLinearMap n a).measurable.comp hYm
  · exact hYg.map (gaussianEnergyLinearMap n a)
  · change (∫ ω, gaussianEnergyLinearMap n a (Y ω) ∂(volume : Measure Ω)) = 0
    rw [(gaussianEnergyLinearMap n a).integral_comp_comm hYg.integrable, hY0]
    simp

theorem gaussianCoordinateEnergy_covariance {Ω I : Type*}
    [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)] [Fintype I] [DecidableEq I]
    (n : ℕ) (X : I → Ω → ℝ) (a : SKConfiguration n → I → ℝ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, (volume : Measure Ω).map (X i) = gaussianReal 0 1)
    (hI : iIndepFun X (volume : Measure Ω))
    (hG : PhysLean.Probability.GaussianIBP.IsGaussianHilbert (gaussianCoordinateEnergy n X a))
    (σ τ : SKConfiguration n) :
    inner ℝ ((PhysLean.Probability.GaussianIBP.covOp hG) (SpinGlass.std_basis n σ))
      (SpinGlass.std_basis n τ) = ∑ i, a σ i * a τ i := by
  rw [← SpinGlass.GeneralizedLatala.gaussianHilbert_eval_pairing]
  change (∫ ω, (∑ i, a σ i * X i ω) * (∑ j, a τ j * X j ω) ∂(volume : Measure Ω)) = _
  exact independent_standardGaussian_linear_covariance X hXm hX hI _ _

/-- The paper's centered edge energy, corrected by one independent common Gaussian. -/
noncomputable def physicalGaussianSKDisorder (n : ℕ) (β h : ℝ) :
    SpinGlass.SKDisorder (Ω := PhysicalSKGaussianSpace) n β h := by
  let X : Option (SKEdge n) → PhysicalSKGaussianSpace → ℝ :=
    fun k ω => physicalSKCoordinates n ω k
  let a : SKConfiguration n → Option (SKEdge n) → ℝ := physicalSKCoefficient n β
  have hXm : ∀ k, Measurable (X k) := fun k => measurable_pi_apply _
  have hX : ∀ k, (volume : Measure PhysicalSKGaussianSpace).map (X k) = gaussianReal 0 1 :=
    fun k => physicalCoordinate_law _
  have hI : iIndepFun X (volume : Measure PhysicalSKGaussianSpace) :=
    physicalSKCoordinates_independent n
  let hG := gaussianCoordinateEnergy_gaussian n X a hXm hX hI
  refine ⟨gaussianCoordinateEnergy n X a, hG, ?_⟩
  intro σ τ
  rw [gaussianCoordinateEnergy_covariance n X a hXm hX hI hG]
  simpa [a, SpinGlass.sk_cov_kernel, SpinGlass.overlap, SpinGlass.spin, spinSign] using
    physicalSKCoefficient_covariance n β σ τ

noncomputable def physicalFieldCoefficient (n : ℕ) (β q : ℝ)
    (σ : SKConfiguration n) (i : Fin n) : ℝ := β * Real.sqrt q * spinSign (σ i)

theorem physicalFieldCoefficient_covariance (n : ℕ) (β q : ℝ) (hq : 0 ≤ q)
    (σ τ : SKConfiguration n) :
    (∑ i, physicalFieldCoefficient n β q σ i * physicalFieldCoefficient n β q τ i) =
      SpinGlass.simple_cov_kernel n β (fun x => q * x) σ τ := by
  have hterm (i : Fin n) :
      physicalFieldCoefficient n β q σ i * physicalFieldCoefficient n β q τ i =
      (β ^ 2 * q) * (spinSign (σ i) * spinSign (τ i)) := by
    unfold physicalFieldCoefficient
    calc
      _ = (β * Real.sqrt q) ^ 2 * (spinSign (σ i) * spinSign (τ i)) := by ring
      _ = _ := by rw [mul_pow, Real.sq_sqrt hq]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  by_cases hn : n = 0
  · subst n
    simp [SpinGlass.simple_cov_kernel]
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [SpinGlass.simple_cov_kernel, SpinGlass.overlap, SpinGlass.spin, spinSign]
  field_simp [hnr]

/-- An independent Gaussian site field supplies the reference disorder. -/
noncomputable def physicalGaussianSimpleDisorder (n : ℕ) (β q : ℝ) (hq : 0 ≤ q) :
    SpinGlass.SimpleDisorder (Ω := PhysicalSKGaussianSpace) n β q := by
  let X : Fin n → PhysicalSKGaussianSpace → ℝ := fun i ω => physicalFieldCoordinates n ω i
  let a : SKConfiguration n → Fin n → ℝ := physicalFieldCoefficient n β q
  have hXm : ∀ i, Measurable (X i) := fun i => measurable_pi_apply _
  have hX : ∀ i, (volume : Measure PhysicalSKGaussianSpace).map (X i) = gaussianReal 0 1 :=
    fun i => physicalCoordinate_law _
  have hI : iIndepFun X (volume : Measure PhysicalSKGaussianSpace) :=
    physicalFieldCoordinates_independent n
  let hG := gaussianCoordinateEnergy_gaussian n X a hXm hX hI
  refine ⟨gaussianCoordinateEnergy n X a, hG, ?_⟩
  intro σ τ
  rw [gaussianCoordinateEnergy_covariance n X a hXm hX hI hG]
  exact physicalFieldCoefficient_covariance n β q hq σ τ

theorem physicalGaussianDisorders_independent (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    IndepFun (physicalGaussianSKDisorder n β h).U
      (physicalGaussianSimpleDisorder n β q hq).V
      (volume : Measure PhysicalSKGaussianSpace) := by
  classical
  let gi : Option (SKEdge n) → (ℕ × ℕ) ⊕ ℕ := fun k => Sum.inl (physicalSKCoordinateIndex k)
  let zi : Fin n → (ℕ × ℕ) ⊕ ℕ := fun i => Sum.inr i.val
  let S : Finset ((ℕ × ℕ) ⊕ ℕ) := Finset.univ.image gi
  let T : Finset ((ℕ × ℕ) ⊕ ℕ) := Finset.univ.image zi
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro k hkS hkT
    simp only [S, T, Finset.mem_image, Finset.mem_univ, true_and] at hkS hkT
    obtain ⟨i, rfl⟩ := hkS
    obtain ⟨j, hj⟩ := hkT
    simp [gi, zi] at hj
  have hg := physicalCoordinates_independent.indepFun_finset S T hST
    (fun _ => measurable_pi_apply _)
  let φ : (S → ℝ) → SpinGlass.EnergySpace n := fun x =>
    gaussianEnergyLinearMap n (physicalSKCoefficient n β)
      (fun k => x ⟨gi k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩)
  let ψ : (T → ℝ) → SpinGlass.EnergySpace n := fun x =>
    gaussianEnergyLinearMap n (physicalFieldCoefficient n β q)
      (fun i => x ⟨zi i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  have hφ : Measurable φ :=
    (gaussianEnergyLinearMap n (physicalSKCoefficient n β)).measurable.comp
      (measurable_pi_iff.mpr fun k => measurable_pi_apply _)
  have hψ : Measurable ψ :=
    (gaussianEnergyLinearMap n (physicalFieldCoefficient n β q)).measurable.comp
      (measurable_pi_iff.mpr fun i => measurable_pi_apply _)
  have hc := hg.comp hφ hψ
  exact hc

/-- A fully concrete smart-path disorder on one fixed probability space. -/
noncomputable def physicalGaussianPath (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    SpinGlass.AT.RSSmartPathDisorder PhysicalSKGaussianSpace n β h q :=
  ⟨physicalGaussianSKDisorder n β h, physicalGaussianSimpleDisorder n β q hq,
    physicalGaussianDisorders_independent n β h q hq⟩

/-- The corrected external endpoint agrees pointwise with the displayed paper energy. -/
theorem physicalGaussianPath_endpoint_apply (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q)
    (ω : PhysicalSKGaussianSpace) (σ : SKConfiguration n) :
    SpinGlass.AT.fullPathHamiltonian (physicalGaussianPath n β h q hq) 1 ω σ =
      physicalCorrectedEnergy β h (fun e => physicalSKCoordinates n ω (some e))
        (physicalSKCoordinates n ω none) σ := by
  change (Real.sqrt 1 • (physicalGaussianSKDisorder n β h).U ω +
    Real.sqrt (1 - 1) • (physicalGaussianSimpleDisorder n β q hq).V ω +
    SpinGlass.magnetic_field_vector n h) σ = _
  simp only [Real.sqrt_one, sub_self, Real.sqrt_zero, one_smul, zero_smul, add_zero]
  change (∑ k, physicalSKCoefficient n β σ k * physicalSKCoordinates n ω k) +
    h * ∑ i, spinSign (σ i) = _
  rw [Fintype.sum_option]
  unfold physicalCorrectedEnergy skHamiltonian
  simp only [physicalSKCoefficient]
  have he : (∑ e : SKEdge n,
      -(β / Real.sqrt (n : ℝ)) * spinSign (σ e.val.1) * spinSign (σ e.val.2) *
        physicalSKCoordinates n ω (some e)) =
      -(β / Real.sqrt (n : ℝ) * ∑ e : SKEdge n,
        physicalSKCoordinates n ω (some e) * spinSign (σ e.val.1) * spinSign (σ e.val.2)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [he]
  ring

/-- Exact equality with the paper's unordered-pair finite free energy. -/
theorem physicalGaussianPath_freeEnergy_eq (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    SpinGlass.AT.skFreeEnergy (physicalGaussianPath n β h q hq) = finiteSKFreeEnergy β h n := by
  let f : (Option (SKEdge n) → ℝ) → ℝ := fun x =>
    Real.log (∑ σ : SKConfiguration n,
      Real.exp (-physicalCorrectedEnergy β h (fun e => x (some e)) (x none) σ))
  have hfm : Measurable f := by
    unfold f physicalCorrectedEnergy skHamiltonian
    fun_prop
  have hcm : Measurable (physicalSKCoordinates n) := by
    change Measurable (fun (ω : PhysicalSKGaussianSpace) (k : Option (SKEdge n)) =>
      ω (Sum.inl (physicalSKCoordinateIndex k)))
    exact measurable_pi_iff.mpr fun k => measurable_pi_apply _
  have hmap := integral_map (μ := (volume : Measure PhysicalSKGaussianSpace)) hcm.aemeasurable hfm.aestronglyMeasurable
  rw [physicalSKCoordinates_law] at hmap
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option (SKEdge n) => ℝ)
  have hemap := integral_map (μ := (skCouplingLaw n).prod (gaussianReal 0 1))
    e.symm.measurable.aemeasurable hfm.aestronglyMeasurable
  have helaw : ((skCouplingLaw n).prod (gaussianReal 0 1)).map e.symm =
      Measure.pi (fun _ : Option (SKEdge n) => gaussianReal 0 1) :=
    Measure.pi_map_piOptionEquivProd (fun _ : Option (SKEdge n) => gaussianReal 0 1)
  rw [helaw] at hemap
  have heval (p : SKCouplings n × ℝ) : f (e.symm p) =
      Real.log (∑ σ, Real.exp (-physicalCorrectedEnergy β h p.1 p.2 σ)) := by
    rfl
  unfold SpinGlass.AT.skFreeEnergy SpinGlass.AT.pathFreeEnergy SpinGlass.free_energy_density SpinGlass.Z
  simp_rw [physicalGaussianPath_endpoint_apply]
  rw [integral_const_mul]
  change (1 / (n : ℝ)) * (∫ ω, f (physicalSKCoordinates n ω) ∂(volume : Measure PhysicalSKGaussianSpace)) = _
  rw [← hmap, hemap]
  simp_rw [heval]
  exact physicalCorrectedFreeEnergy_eq β h

end Paper
