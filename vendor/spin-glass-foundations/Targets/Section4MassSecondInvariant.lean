module

public import Targets.CoupledReplicaWeights
public import Targets.CoupledCascadeSecond

@[expose] public section

/-!
# A depth-preserving second-derivative estimate for normalized Gaussian tilts

The covariance term uses the variance of the first derivative. Keeping that
variance together with the square of its mean avoids a factor at every level.
All masses in `[0,1]`, including zero, are supported.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

private theorem mean_add {n : ℕ} {A G H : (Fin n → ℝ) → ℝ} {B C m v : ℝ}
    (hA : GuerraGrowth A) (hG : Measurable G) (hH : Measurable H)
    (hb : ∀ y, |G y| ≤ B) (hc : ∀ y, |H y| ≤ C) (x : Fin n → ℝ) :
    pairedTiltMean m v A (fun y => G y + H y) x =
      pairedTiltMean m v A G x + pairedTiltMean m v A H x := by
  simp only [pairedTiltMean, add_mul]
  exact integral_add (integrable_pairedTiltMean hA hG hb x)
    (integrable_pairedTiltMean hA hH hc x)

private theorem mean_const_mul {n : ℕ} (A G : (Fin n → ℝ) → ℝ)
    (m v c : ℝ) (x : Fin n → ℝ) :
    pairedTiltMean m v A (fun y => c * G y) x = c * pairedTiltMean m v A G x := by
  simp only [pairedTiltMean, mul_assoc, integral_const_mul]

private theorem mean_mono {n : ℕ} {A G H : (Fin n → ℝ) → ℝ} {B C m v : ℝ}
    (hA : GuerraGrowth A) (hG : Measurable G) (hH : Measurable H)
    (hb : ∀ y, |G y| ≤ B) (hc : ∀ y, |H y| ≤ C) (hle : ∀ y, G y ≤ H y)
    (x : Fin n → ℝ) : pairedTiltMean m v A G x ≤ pairedTiltMean m v A H x := by
  obtain ⟨CA, L, hL, hAb⟩ := hA.bound
  exact integral_mono (integrable_pairedTiltMean hA hG hb x)
    (integrable_pairedTiltMean hA hH hc x) fun z =>
      mul_le_mul_of_nonneg_right (hle _) (tiltWeightPi_nonneg hL hAb hA.measurable x z)

/-- Jensen's square estimate for the actual normalized Gaussian tilt. -/
theorem pairedTiltMean_sq_le {n : ℕ} {A D : (Fin n → ℝ) → ℝ} {B m v : ℝ}
    (hA : GuerraGrowth A) (hD : Measurable D) (hb : ∀ y, |D y| ≤ B) (x : Fin n → ℝ) :
    pairedTiltMean m v A D x ^ 2 ≤ pairedTiltMean m v A (fun y => D y ^ 2) x := by
  let d := pairedTiltMean m v A D x
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb x)
  have hb₂ (y) : |D y ^ 2| ≤ B ^ 2 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb y) 2
  have hpos := pairedTiltMean_nonneg hA (fun y => sq_nonneg (D y - d)) m v x
  have he : (fun y => (D y - d) ^ 2) = fun y => D y ^ 2 + (-2 * d) * D y + d ^ 2 := by
    funext y; ring
  rw [he, mean_add (G := fun z => D z ^ 2 + (-2 * d) * D z) (H := fun _ => d ^ 2)
      hA ((hD.pow_const 2).add (hD.const_mul _)) measurable_const
      (fun y => (abs_add_le _ _).trans (add_le_add (hb₂ y)
        (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb y) (abs_nonneg _))))
      (fun _ => le_rfl),
    mean_add (G := fun z => D z ^ 2) (H := fun z => (-2 * d) * D z)
      hA (hD.pow_const 2) (hD.const_mul _) hb₂
      (fun y => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb y) (abs_nonneg _)),
    mean_const_mul, pairedTiltMean_const hA] at hpos
  change 0 ≤ pairedTiltMean m v A (fun y => D y ^ 2) x + (-2 * d) * d + d ^ 2 at hpos
  change d ^ 2 ≤ _
  nlinarith

/-- The exact invariant propagated by a second-field mass covariance rule.
The constant does not grow with the number of outer levels. -/
theorem pairedSecondCovariance_mass_invariant {n : ℕ}
    {A D E : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {B C m v : ℝ}
    (hA : CoupledGrowth A)
    (hD : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => D p.1 p.2))
    (hE : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => E p.1 p.2))
    (hb : ∀ x y, |D x y| ≤ B) (hC : ∀ x y, |E x y| + D x y ^ 2 ≤ C)
    (hm : m ∈ Set.Icc 0 1) (x y : Fin n → ℝ) :
    |pairedSecondCovariance m v A D D E x y| + pairedSecondMean m v A D x y ^ 2 ≤ C := by
  let M := fun G => pairedTiltMean m v (A x) G y
  let d := M (D x)
  let q := M (fun z => D x z ^ 2)
  let e := M (E x)
  let a := M (fun z => |E x z|)
  have hDx : Measurable (D x) := hD.comp (measurable_const.prodMk measurable_id)
  have hEx : Measurable (E x) := hE.comp (measurable_const.prodMk measurable_id)
  have hAx := hA.section_right x
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb x y)
  have hC0 : 0 ≤ C := (add_nonneg (abs_nonneg _) (sq_nonneg _)).trans (hC x y)
  have hbE (z) : |E x z| ≤ C := by nlinarith [hC x z, sq_nonneg (D x z)]
  have hbD₂ (z) : |D x z ^ 2| ≤ B ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb x z) 2
  have hq : d ^ 2 ≤ q := pairedTiltMean_sq_le hAx hDx (hb x) y
  have hsum : a + q ≤ C := by
    have H := mean_mono (m := m) (v := v) (G := fun z => |E x z| + D x z ^ 2)
      hAx (hEx.abs.add (hDx.pow_const 2)) measurable_const
      (fun z => (abs_add_le _ _).trans (add_le_add (by simpa only [abs_abs] using hbE z) (hbD₂ z)))
      (fun _ => le_rfl) (hC x) y
    rw [mean_add (G := fun z => |E x z|) (H := fun z => D x z ^ 2)
      hAx hEx.abs (hDx.pow_const 2) (fun z => by simpa only [abs_abs] using hbE z)
      hbD₂, pairedTiltMean_const hAx] at H
    exact H
  have hea : |e| ≤ a := by
    obtain ⟨CA, L, hL, hAb⟩ := hAx.bound
    have H := abs_integral_le_integral_abs (f := fun z => E x (fun i => y i + Real.sqrt v * z i) *
      tiltWeightPi n m v (A x) y z) (μ := piGauss n)
    simpa only [e, a, M, pairedTiltMean, abs_mul,
      abs_of_nonneg (tiltWeightPi_nonneg hL hAb hAx.measurable y _)] using H
  have heq : pairedSecondCovariance m v A D D E x y = e + m * (q - d ^ 2) := by
    unfold pairedSecondCovariance pairedSecondMean
    dsimp only
    have hf : (fun z => E x z + m * D x z * D x z) = fun z => E x z + m * (D x z ^ 2) := by
      funext z; ring
    rw [hf, mean_add (G := E x) (H := fun z => m * D x z ^ 2)
      hAx hEx ((hDx.pow_const 2).const_mul m) hbE
      (fun z => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hbD₂ z) (abs_nonneg m)), mean_const_mul]
    change e + m * q - m * d * d = _
    ring
  rw [heq]
  change |e + m * (q - d ^ 2)| + d ^ 2 ≤ C
  have hvar : 0 ≤ m * (q - d ^ 2) := mul_nonneg hm.1 (sub_nonneg.mpr hq)
  have htri := abs_add_le e (m * (q - d ^ 2))
  rw [abs_of_nonneg hvar] at htri
  have hmvar := mul_le_of_le_one_left (sub_nonneg.mpr hq) hm.2
  nlinarith

end SpinGlass.Targets
