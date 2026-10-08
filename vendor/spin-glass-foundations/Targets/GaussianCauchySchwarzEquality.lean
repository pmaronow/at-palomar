module

public import Targets.ParisiStrictConvexity
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
# Equality in Gaussian Cauchy--Schwarz

For the strict paired comparison in Talagrand §5, equality must identify
the continuous profiles everywhere, not merely almost everywhere. The
normalized-square proof reuses Gaussian absolute continuity with Lebesgue
measure; no full-support or equality-case hypothesis is added.
-/

open MeasureTheory ProbabilityTheory Real Filter

namespace SpinGlass.Targets

/-- Equality in Gaussian Cauchy--Schwarz forces proportional continuous
profiles. The second profile is positive so its squared norm is nonzero. -/
theorem eq_mul_of_gaussian_cauchySchwarz_eq {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hgpos : ∀ z, 0 < g z)
    (hff : Integrable (fun z => f z ^ 2) (gaussianReal 0 1))
    (hgg : Integrable (fun z => g z ^ 2) (gaussianReal 0 1))
    (hfg : Integrable (fun z => f z * g z) (gaussianReal 0 1))
    (he : (∫ z, f z * g z ∂gaussianReal 0 1) ^ 2 =
      (∫ z, f z ^ 2 ∂gaussianReal 0 1) * (∫ z, g z ^ 2 ∂gaussianReal 0 1)) :
    ∃ c : ℝ, ∀ z, f z = c * g z := by
  let E := ∫ z, g z ^ 2 ∂gaussianReal 0 1
  let P := ∫ z, f z * g z ∂gaussianReal 0 1
  let Q := ∫ z, f z ^ 2 ∂gaussianReal 0 1
  have hE : 0 < E := by
    apply (integral_pos_iff_support_of_nonneg (fun z => sq_nonneg (g z)) hgg).mpr
    have hs : Function.support (fun z => g z ^ 2) = Set.univ := by
      ext z
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (sq_pos_of_pos (hgpos z)).ne'
    rw [hs]
    simp
  let c := P / E
  have hsub : Integrable (fun z => f z ^ 2 - (2 * c) * (f z * g z))
      (gaussianReal 0 1) := hff.sub (hfg.const_mul (2 * c))
  have hlast : Integrable (fun z => c ^ 2 * g z ^ 2) (gaussianReal 0 1) :=
    hgg.const_mul (c ^ 2)
  have hi : Integrable (fun z => (f z - c * g z) ^ 2) (gaussianReal 0 1) := by
    convert! hsub.add hlast using 1
    funext z
    simp only [Pi.add_apply]
    ring
  have hz : (∫ z, (f z - c * g z) ^ 2 ∂gaussianReal 0 1) = 0 := by
    have hexpand : (fun z => (f z - c * g z) ^ 2) =
        fun z => f z ^ 2 - (2 * c) * (f z * g z) + c ^ 2 * g z ^ 2 := by
      funext z
      ring
    rw [hexpand, integral_add hsub hlast,
      integral_sub hff (hfg.const_mul (2 * c)), integral_const_mul, integral_const_mul]
    change Q - (2 * c) * P + c ^ 2 * E = 0
    have hPQ : P ^ 2 = Q * E := he
    dsimp [c]
    field_simp
    nlinarith
  have hae : (fun z => (f z - c * g z) ^ 2) =ᵐ[gaussianReal 0 1] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hi).mp hz
  have hv : (fun z => (f z - c * g z) ^ 2) =ᵐ[volume] 0 :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0)).ae_eq hae
  have hall := MeasureTheory.Measure.eq_of_ae_eq hv ((hf.sub (hg.const_mul c)).pow 2) continuous_const
  refine ⟨c, fun z => ?_⟩
  have hh := congrFun hall z
  change (f z - c * g z) ^ 2 = 0 at hh
  nlinarith [sq_nonneg (f z - c * g z)]

end SpinGlass.Targets
