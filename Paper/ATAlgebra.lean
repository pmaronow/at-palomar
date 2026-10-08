module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Algebra in the appendix of arXiv:2604.11921v2

These lemmas prove the appendix's finite-dimensional algebra and sign arguments.
Their hypotheses are explicit. In particular, they do not assume or assert
Gaussian integration by parts, differentiability under an integral, or the
existence of the smooth AT curve.
-/

namespace Paper

/-- The zero-set quantity in the appendix. `A,C` stand for the two Gaussian
expectations, but this algebraic definition does not require an integration
theory. -/
def atZeroQuantity (t A C : ℝ) : ℝ := t * C + A - 1

/-- An AT-critical RS fixed point gives a zero of the appendix's `F`. -/
theorem at_critical_gives_zero (β q A C : ℝ)
    (hfixed : q = 1 - A) (hcritical : β ^ 2 * C = 1) :
    atZeroQuantity (β ^ 2 * q) A C = 0 := by
  unfold atZeroQuantity
  calc
    (β ^ 2 * q) * C + A - 1 = (β ^ 2 * C) * q + A - 1 := by ring
    _ = 0 := by rw [hcritical, hfixed]; ring

/-- The zero equation is exactly the fixed-point relation for `q = t C`. -/
theorem at_zero_iff_fixed_point (t A C : ℝ) :
    atZeroQuantity t A C = 0 ↔ t * C = 1 - A := by
  unfold atZeroQuantity
  constructor <;> intro h <;> linarith

/-- The reconstructed fixed point lies in `(0,1)` when `A` does. -/
theorem at_zero_fixed_point_bounds (t A C : ℝ)
    (hzero : atZeroQuantity t A C = 0) (hApos : 0 < A) (hAlt : A < 1) :
    0 < t * C ∧ t * C < 1 := by
  have hfixed := (at_zero_iff_fixed_point t A C).mp hzero
  constructor <;> linarith

/-- Reconstruct the squared inverse-temperature and time coordinates. -/
theorem at_zero_reconstruction (t A C : ℝ) (hC : 0 < C)
    (hzero : atZeroQuantity t A C = 0) :
    (1 / C) * C = 1 ∧ (1 / C) * (t * C) = t ∧ t * C = 1 - A := by
  have hCne : C ≠ 0 := ne_of_gt hC
  refine ⟨by field_simp, ?_, (at_zero_iff_fixed_point t A C).mp hzero⟩
  field_simp

/-- The nonnegative square-root coordinate used in the reverse AT map
satisfies the criticality equation. -/
theorem at_sqrt_coordinate_critical (C : ℝ) (hC : 0 < C) :
    (Real.sqrt (1 / C)) ^ 2 * C = 1 := by
  rw [Real.sq_sqrt (le_of_lt (one_div_pos.mpr hC))]
  exact (at_zero_reconstruction 0 1 C hC (by simp [atZeroQuantity])).1

/-- The Gaussian arguments coincide after reconstruction:
`β sqrt(q) = sqrt(t)` for `β = sqrt(1/C)` and `q = t C`. -/
theorem at_sqrt_argument (t C : ℝ) (hC : 0 < C) :
    Real.sqrt (1 / C) * Real.sqrt (t * C) = Real.sqrt t := by
  have hCne : C ≠ 0 := ne_of_gt hC
  rw [← Real.sqrt_mul (le_of_lt (one_div_pos.mpr hC))]
  congr 1
  field_simp

/-- On the zero set, positivity of `A` forces `β² = 1/C > t`. -/
theorem at_inverse_temperature_bound (t A C : ℝ) (hC : 0 < C)
    (hA : 0 < A) (hzero : atZeroQuantity t A C = 0) :
    t < 1 / C := by
  have hfixed := (at_zero_iff_fixed_point t A C).mp hzero
  apply (lt_div_iff₀ hC).mpr
  linarith

/-- Positivity of the denominator appearing in the slope of the zero curve. -/
theorem at_slope_denominator_pos (t u v : ℝ) (ht : 0 < t)
    (hu : 0 < u) (hv : 0 < v) :
    0 < u + 2 * t * v := by positivity

/-- The partial derivative `F_h = -2u-4tv` is strictly negative. -/
theorem at_field_derivative_neg (t u v : ℝ) (ht : 0 < t)
    (hu : 0 < u) (hv : 0 < v) :
    -2 * u - 4 * t * v < 0 := by
  have htv : 0 < t * v := mul_pos ht hv
  nlinarith

/-- The partial derivative `F_t = 2(B-T+hv)` is strictly positive. -/
theorem at_time_derivative_pos (h B T v : ℝ) (hh : 0 ≤ h)
    (hBT : T < B) (hv : 0 ≤ v) :
    0 < 2 * (B - T + h * v) := by
  have hhv : 0 ≤ h * v := mul_nonneg hh hv
  linarith

/-- The implicit slope `h'(t)` is positive under the appendix's signs. -/
theorem at_curve_slope_pos (h t B T u v : ℝ) (hh : 0 ≤ h)
    (ht : 0 < t) (hBT : T < B) (hu : 0 < u) (hv : 0 < v) :
    0 < (B - T + h * v) / (u + 2 * t * v) := by
  have hhv : 0 ≤ h * v := mul_nonneg hh (le_of_lt hv)
  have hnum : 0 < B - T + h * v := by linarith
  exact div_pos hnum (at_slope_denominator_pos t u v ht hu hv)

/-- Exact simplification of the total derivative of `C` on the zero curve. -/
theorem at_curve_derivative_identity (h t B T u v : ℝ)
    (ht : t ≠ 0) (hden : u + 2 * t * v ≠ 0) :
    2 * (h * v - T) / t - 4 * v * (B - T + h * v) / (u + 2 * t * v) =
      -(2 * (u * T + v * (2 * t * B - h * u))) / (t * (u + 2 * t * v)) := by
  set d : ℝ := u + 2 * t * v
  have hd : d ≠ 0 := hden
  field_simp [ht, hd]
  dsimp [d]
  ring

/-- The simplified total derivative of `C` is negative, once its analytic
ingredients have supplied the four strict signs. -/
theorem at_curve_derivative_neg (h t B T u v : ℝ)
    (ht : 0 < t) (hu : 0 < u) (hv : 0 < v) (hT : 0 < T)
    (hgap : 0 < 2 * t * B - h * u) :
    2 * (h * v - T) / t - 4 * v * (B - T + h * v) / (u + 2 * t * v) < 0 := by
  have hden := at_slope_denominator_pos t u v ht hu hv
  rw [at_curve_derivative_identity h t B T u v (ne_of_gt ht) (ne_of_gt hden)]
  have hnum : 0 < 2 * (u * T + v * (2 * t * B - h * u)) := by positivity
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) (mul_pos ht hden)

/-- The derivative of `C⁻¹/²`, written without real powers, is positive when
`C` is positive and its derivative is negative. -/
theorem at_beta_derivative_pos (C D : ℝ) (hC : 0 < C) (hD : D < 0) :
    0 < -(D / (2 * C * Real.sqrt C)) := by
  apply neg_pos.mpr
  exact div_neg_of_neg_of_pos hD (by positivity)

/-- The second integration-by-parts rearrangement is purely algebraic after
the Gaussian identity and the zero equation are available. -/
theorem at_ibp_gap_identity (h t A C u E : ℝ)
    (hzero : atZeroQuantity t A C = 0)
    (hIBP : E = h * u + t * (3 * C - 2 * A)) :
    2 * t * (A - C) - h * u = (1 - A) - E := by
  have hfixed := (at_zero_iff_fixed_point t A C).mp hzero
  rw [hIBP, ← hfixed]
  ring

/-- Conditional calculus consequence of the appendix's derivative formula:
once the Gaussian and implicit-function analysis has supplied this derivative
and the signs, its zero curve is strictly increasing. -/
theorem at_curve_strictMono_of_derivative
    (H B T u v : ℝ → ℝ)
    (hH : ∀ t > 0, 0 ≤ H t)
    (hBT : ∀ t > 0, T t < B t)
    (hu : ∀ t > 0, 0 < u t)
    (hv : ∀ t > 0, 0 < v t)
    (hderiv : ∀ t > 0, HasDerivAt H
      ((B t - T t + H t * v t) / (u t + 2 * t * v t)) t) :
    StrictMonoOn H (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  · intro t ht
    have htpos : 0 < t := by simpa only [interior_Ioi, Set.mem_Ioi] using ht
    rw [(hderiv t htpos).deriv]
    exact at_curve_slope_pos (H t) t (B t) (T t) (u t) (v t)
      (hH t htpos) htpos (hBT t htpos) (hu t htpos) (hv t htpos)

/-- Conditional calculus consequence for the Gaussian fourth moment along
the zero curve. -/
theorem at_C_curve_strictAnti_of_derivative
    (H C B T u v : ℝ → ℝ)
    (hu : ∀ t > 0, 0 < u t)
    (hv : ∀ t > 0, 0 < v t)
    (hT : ∀ t > 0, 0 < T t)
    (hgap : ∀ t > 0, 0 < 2 * t * B t - H t * u t)
    (hderiv : ∀ t > 0, HasDerivAt C
      (2 * (H t * v t - T t) / t -
        4 * v t * (B t - T t + H t * v t) / (u t + 2 * t * v t)) t) :
    StrictAntiOn C (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  · intro t ht
    have htpos : 0 < t := by simpa only [interior_Ioi, Set.mem_Ioi] using ht
    rw [(hderiv t htpos).deriv]
    exact at_curve_derivative_neg (H t) t (B t) (T t) (u t) (v t)
      htpos (hu t htpos) (hv t htpos) (hT t htpos) (hgap t htpos)

/-- The endpoint estimate `β(t)²>t` forces `β(t)→∞` provided the chosen
inverse-temperature coordinate is nonnegative. -/
theorem at_beta_tendsto_atTop (β : ℝ → ℝ)
    (hβ : ∀ t > 0, 0 ≤ β t)
    (hbound : ∀ t > 0, t < β t ^ 2) :
    Filter.Tendsto β Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono' Filter.atTop _ Real.tendsto_sqrt_atTop
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  have hsqrt : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt (le_of_lt ht)
  have hsqrtpos := Real.sqrt_nonneg t
  have hb := hβ t ht
  have hsq := hbound t ht
  nlinarith

/-- IVT and strict decrease give a unique positive zero from a sign change.
This is the fixed-time existence/uniqueness step in the appendix. -/
theorem at_exists_unique_positive_zero (f : ℝ → ℝ) (b : ℝ)
    (hb : 0 < b) (hcont : ContinuousOn f (Set.Icc 0 b))
    (hmono : StrictAntiOn f (Set.Ioi 0)) (hleft : 0 < f 0) (hright : f b < 0) :
    ∃! h : ℝ, 0 < h ∧ f h = 0 := by
  obtain ⟨h, hh, hzero⟩ :=
    intermediate_value_Ioo' (le_of_lt hb) hcont ⟨hright, hleft⟩
  refine ⟨h, ⟨hh.1, hzero⟩, ?_⟩
  intro y hy
  exact hmono.injOn hy.1 hh.1 (hy.2.trans hzero.symm)

/-- The range argument for an inverse-temperature coordinate extended
continuously to `β(0)=1`. -/
theorem at_beta_bijOn (β : ℝ → ℝ) (hβzero : β 0 = 1)
    (hcont : ContinuousOn β (Set.Ici 0))
    (hmono : StrictMonoOn β (Set.Ici 0))
    (hβ : ∀ t > 0, 0 ≤ β t)
    (hbound : ∀ t > 0, t < β t ^ 2) :
    Set.BijOn β (Set.Ioi 0) (Set.Ioi 1) := by
  have himage : β '' Set.Ioi 0 = Set.Ioi 1 := by
    simpa only [hβzero] using
      hcont.image_Ioi_of_strictMonoOn hmono (at_beta_tendsto_atTop β hβ hbound)
  refine ⟨?_, hmono.injOn.mono Set.Ioi_subset_Ici_self, ?_⟩
  · intro t ht
    rw [← himage]
    exact ⟨t, ht, rfl⟩
  · intro b hb
    rw [← himage] at hb
    exact hb

/-- After constructing the inverse time coordinate, its composition with the
field curve has the monotonicity asserted for `h_AT`. -/
theorem at_boundary_strictMono (H time : ℝ → ℝ)
    (hH : StrictMonoOn H (Set.Ioi 0))
    (htime : StrictMonoOn time (Set.Ioi 1))
    (htimepos : ∀ β > 1, 0 < time β) :
    StrictMonoOn (fun β => H (time β)) (Set.Ioi 1) := by
  intro a ha b hb hab
  exact hH (htimepos a ha) (htimepos b hb) (htime ha hb hab)

end Paper
