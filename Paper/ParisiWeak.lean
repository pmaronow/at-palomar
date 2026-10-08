module

public import Paper.ParisiMildDerivative
public import Paper.ParisiTestRegularity
public import Paper.HeatAdjoint

@[expose] public section

/-!
# Distributional spatial derivatives of the constructed Parisi potential

The weak gradient is verified against actual smooth compactly supported
tests.  Spatial integration by parts and absolute integrability on the
time-space product discharge the distributional identity.
-/

open Set MeasureTheory ProbabilityTheory
open scoped Topology ContDiff

namespace Paper

instance : IsLocallyFiniteMeasure parisiSpaceTime := by
  unfold parisiSpaceTime
  infer_instance

theorem hasCompactSupport_spatial_section (φ : ℝ × ℝ → ℝ)
    (hc : HasCompactSupport φ) (t : ℝ) : HasCompactSupport (fun x : ℝ => φ (t, x)) := by
  have hk : IsCompact (Prod.snd '' tsupport φ) := hc.image continuous_snd
  apply hk.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hk.isClosed
  intro x hx
  exact ⟨(t, x), subset_closure hx, rfl⟩

/-- A genuine classical spatial derivative supplies the distributional
spatial gradient. The potential is allowed to grow at infinity. -/
theorem isParisiWeakGradient_of_hasDerivAt (u v : ℝ × ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      HasDerivAt (fun y => u (t, y)) (v (t, x)) x) : IsParisiWeakGradient u v := by
  intro φ hφ hc _
  have hx : Continuous (parisiTestX φ) := continuous_parisiTestX φ hφ
  have hxc : HasCompactSupport (parisiTestX φ) := hasCompactSupport_parisiTestX φ hφ hc
  have hi : Integrable (fun p => u p * parisiTestX φ p) parisiSpaceTime :=
    (hu.mul hx).integrable_of_hasCompactSupport hxc.mul_left
  have hj : Integrable (fun p => v p * φ p) parisiSpaceTime :=
    (hv.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  refine ⟨hi.add hj, ?_⟩
  unfold parisiSpaceTime at hi hj ⊢
  rw [integral_prod (fun p : ℝ × ℝ => u p * parisiTestX φ p + v p * φ p) (hi.add hj)]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hup : Continuous (fun x : ℝ => u (t, x)) := hu.comp (by fun_prop)
  have hvp : Continuous (fun x : ℝ => v (t, x)) := hv.comp (by fun_prop)
  have hfp : Continuous (fun x : ℝ => φ (t, x)) := hφ.continuous.comp (by fun_prop)
  have hxp : Continuous (fun x : ℝ => parisiTestX φ (t, x)) := hx.comp (by fun_prop)
  have hfc := hasCompactSupport_spatial_section φ hc t
  have hxxc := hasCompactSupport_spatial_section (parisiTestX φ) hxc t
  have hux : Integrable (fun x : ℝ => u (t, x) * parisiTestX φ (t, x)) :=
    (hup.mul hxp).integrable_of_hasCompactSupport hxxc.mul_left
  have hvf : Integrable (fun x : ℝ => v (t, x) * φ (t, x)) :=
    (hvp.mul hfp).integrable_of_hasCompactSupport hfc.mul_left
  have huf : Integrable (fun x : ℝ => u (t, x) * φ (t, x)) :=
    (hup.mul hfp).integrable_of_hasCompactSupport hfc.mul_left
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x => u (t, x)) (u' := fun x => v (t, x))
    (v := fun x => φ (t, x)) (v' := fun x => parisiTestX φ (t, x))
    (fun x _ => hd t ht x) (fun x _ => hasDerivAt_parisiTestX φ hφ t x)
    hux hvf huf
  rw [integral_add hux hvf, hibp]
  simp

end Paper
