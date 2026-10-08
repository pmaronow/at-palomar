module

/- Dependency adaptation: import only SK/Gaussian-law foundations for this Gaussian constructor, avoiding an unnecessary dependency on the strict-AT main theorem. -/
public import Lemmas.SpinGlass.SKModel
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

open MeasureTheory ProbabilityTheory BigOperators
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace PhysLean.Probability.GaussianIBP

variable {Ω H : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (volume : Measure Ω)]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ H]

/-- A measurable centered finite-dimensional Gaussian vector supplies the
spectral data expected by `IsGaussianHilbert`. -/
noncomputable def IsGaussianHilbert.of_hasGaussianLaw
    (G : Ω → H) (hGm : Measurable G)
    (hG : HasGaussianLaw G (volume : Measure Ω))
    (hG0 : ∫ ω, G ω ∂(volume : Measure Ω) = 0) :
    IsGaussianHilbert G := by
  let μ : Measure H := Measure.map G (volume : Measure Ω)
  let T : H →L[ℝ] H := covarianceOperator μ
  have hTpos : T.toLinearMap.IsPositive := by
    simpa [T] using (isPositive_covarianceOperator (μ := μ))
  have hTsym : T.toLinearMap.IsSymmetric := hTpos.isSymmetric
  let w : OrthonormalBasis (Fin (Module.finrank ℝ H)) ℝ H :=
    hTsym.eigenvectorBasis rfl
  let eig : Fin (Module.finrank ℝ H) → ℝ := hTsym.eigenvalues rfl
  have heig_nonneg (i : Fin (Module.finrank ℝ H)) : 0 ≤ eig i := by
    have hp := hTpos.right (w i)
    have he := hTsym.apply_eigenvectorBasis rfl i
    change 0 ≤ inner ℝ (T (w i)) (w i) at hp
    change T (w i) = eig i • w i at he
    rw [he] at hp
    simpa [real_inner_smul_left] using hp
  let c : Fin (Module.finrank ℝ H) → Ω → ℝ :=
    fun i ω => inner ℝ (w i) (G ω)
  have hGint : Integrable G (volume : Measure Ω) := hG.integrable
  have hc_mean (i : Fin (Module.finrank ℝ H)) :
      ∫ ω, c i ω ∂(volume : Measure Ω) = 0 := by
    let L : H →L[ℝ] ℝ := ContinuousLinearMap.innerSL ℝ (w i)
    calc
      ∫ ω, c i ω ∂(volume : Measure Ω) =
          L (∫ ω, G ω ∂(volume : Measure Ω)) := by
            simpa [c, L] using L.integral_comp_comm hGint
      _ = 0 := by simp [hG0]
  have hμ2 : MemLp id 2 μ := by
    haveI : IsGaussian μ := hG.isGaussian_map
    exact IsGaussian.memLp_two_id
  have hc_variance (i : Fin (Module.finrank ℝ H)) :
      Var[c i; (volume : Measure Ω)] = eig i := by
    have hcm : Measurable (c i) := by
      exact (ContinuousLinearMap.innerSL ℝ (w i)).measurable.comp hGm
    rw [variance_eq_integral hcm.aemeasurable, hc_mean]
    simp only [sub_zero, pow_two]
    calc
      ∫ ω, c i ω * c i ω ∂(volume : Measure Ω) =
          ∫ x, inner ℝ (w i) x * inner ℝ (w i) x ∂μ := by
            symm
            exact integral_map hGm.aemeasurable
              (Measurable.aestronglyMeasurable (by fun_prop))
      _ = inner ℝ (T (w i)) (w i) := by
            symm
            simpa [T] using covarianceOperator_inner hμ2 (w i) (w i)
      _ = eig i := by
            change inner ℝ
              (T ((hTsym.eigenvectorBasis rfl) i))
              ((hTsym.eigenvectorBasis rfl) i) = hTsym.eigenvalues rfl i
            have he : T ((hTsym.eigenvectorBasis rfl) i) =
                hTsym.eigenvalues rfl i • (hTsym.eigenvectorBasis rfl) i := by
              change T.toLinearMap ((hTsym.eigenvectorBasis rfl) i) = _
              exact hTsym.apply_eigenvectorBasis rfl i
            rw [he]
            rw [inner_smul_left]
            simp
  have hc_gauss (i : Fin (Module.finrank ℝ H)) :
      IsCenteredGaussianRV (c i) ⟨eig i, heig_nonneg i⟩ := by
    let L : H →L[ℝ] ℝ := ContinuousLinearMap.innerSL ℝ (w i)
    have hci : HasGaussianLaw (c i) (volume : Measure Ω) := by
      simpa [c, L, Function.comp_def] using hG.map L
    unfold IsCenteredGaussianRV IsGaussianRV
    rw [hci.map_eq_gaussianReal, hc_mean, hc_variance]
    rw [Real.toNNReal_of_nonneg (heig_nonneg i)]
    congr
  have hc_joint : HasGaussianLaw (fun ω i => c i ω)
      (volume : Measure Ω) := by
    let L : H →L[ℝ] (Fin (Module.finrank ℝ H) → ℝ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.innerSL ℝ (w i)
    simpa [c, L, Function.comp_def] using hG.map L
  have hc_indep : iIndepFun c (volume : Measure Ω) := by
    apply hc_joint.iIndepFun_of_covariance_inner
    intro i j hij x y
    simp only [RCLike.inner_apply, conj_trivial]
    rw [covariance_mul_const_left, covariance_mul_const_right]
    have hci : MemLp (c i) 2 (volume : Measure Ω) :=
      (hc_joint.eval i).memLp_two
    have hcj : MemLp (c j) 2 (volume : Measure Ω) :=
      (hc_joint.eval j).memLp_two
    have hcov : cov[c i, c j; (volume : Measure Ω)] = 0 := by
      rw [covariance_eq_sub hci hcj, hc_mean, hc_mean]
      simp only [mul_zero, sub_zero]
      calc
        ∫ ω, c i ω * c j ω ∂(volume : Measure Ω) =
            ∫ z, inner ℝ (w i) z * inner ℝ (w j) z ∂μ := by
              symm
              exact integral_map hGm.aemeasurable
                (Measurable.aestronglyMeasurable (by fun_prop))
        _ = inner ℝ (T (w i)) (w j) := by
              symm
              simpa [T] using covarianceOperator_inner hμ2 (w i) (w j)
        _ = 0 := by
              change inner ℝ
                (T ((hTsym.eigenvectorBasis rfl) i))
                ((hTsym.eigenvectorBasis rfl) j) = 0
              have he : T ((hTsym.eigenvectorBasis rfl) i) =
                  hTsym.eigenvalues rfl i • (hTsym.eigenvectorBasis rfl) i := by
                change T.toLinearMap ((hTsym.eigenvectorBasis rfl) i) = _
                exact hTsym.apply_eigenvectorBasis rfl i
              rw [he]
              rw [inner_smul_left]
              simp [hij]
    rw [hcov]
    ring
  exact
    { ι := Fin (Module.finrank ℝ H)
      fintype_ι := inferInstance
      w := w
      τ := fun i => ⟨eig i, heig_nonneg i⟩
      c := c
      c_meas := fun i =>
        (ContinuousLinearMap.innerSL ℝ (w i)).measurable.comp hGm
      c_gauss := hc_gauss
      c_indep := hc_indep
      repr := by
        funext ω
        simpa [c, real_inner_comm] using (w.sum_repr' (G ω)).symm }

end PhysLean.Probability.GaussianIBP
