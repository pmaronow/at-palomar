module

public import Paper.HJBVerification

@[expose] public section

/-! Deterministic time translation preserves the genuine Itô test fields. -/
noncomputable section
open Set MeasureTheory StochasticCalculus
namespace Paper

def itoTimeShift (f : ℝ → ℝ → ℝ) (a : ℝ) (t x : ℝ) : ℝ := f (a + t) x

@[simp] theorem itoTimeShift_spaceDerivative (f : ℝ → ℝ → ℝ) (a t x : ℝ) :
    itoSpaceDerivative (itoTimeShift f a) t x = itoSpaceDerivative f (a + t) x := rfl

@[simp] theorem itoTimeShift_spaceSecondDerivative (f : ℝ → ℝ → ℝ) (a t x : ℝ) :
    itoSpaceSecondDerivative (itoTimeShift f a) t x = itoSpaceSecondDerivative f (a + t) x := rfl

@[simp] theorem itoTimeShift_timeDerivative (f : ℝ → ℝ → ℝ)
    (ht : ∀ x, Differentiable ℝ (fun t => f t x)) (a t x : ℝ) :
    itoTimeDerivative (itoTimeShift f a) t x = itoTimeDerivative f (a + t) x := by
  have hd := ((ht x (a + t)).hasDerivAt).comp t ((hasDerivAt_id t).const_add a)
  simpa only [itoTimeDerivative, itoTimeShift, Function.comp_def, one_mul, mul_one] using hd.deriv

theorem differentiable_itoTimeShift (f : ℝ → ℝ → ℝ)
    (ht : ∀ x, Differentiable ℝ (fun t => f t x)) (a x : ℝ) :
    Differentiable ℝ (fun t => itoTimeShift f a t x) :=
  (ht x).comp (by fun_prop : Differentiable ℝ (fun t : ℝ => a + t))

theorem continuous_itoTimeShift (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => itoTimeShift f a p.1 p.2) :=
  hf.comp ((continuous_const.add continuous_fst).prodMk continuous_snd)

theorem continuous_itoTimeShift_timeDerivative (f : ℝ → ℝ → ℝ)
    (ht : ∀ x, Differentiable ℝ (fun t => f t x))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2)) (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => itoTimeDerivative (itoTimeShift f a) p.1 p.2) := by
  simp only [itoTimeShift_timeDerivative f ht]
  exact hdt.comp ((continuous_const.add continuous_fst).prodMk continuous_snd)

theorem continuous_itoTimeShift_spaceDerivative (f : ℝ → ℝ → ℝ)
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2)) (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => itoSpaceDerivative (itoTimeShift f a) p.1 p.2) :=
  hdx.comp ((continuous_const.add continuous_fst).prodMk continuous_snd)

theorem continuous_itoTimeShift_spaceSecondDerivative (f : ℝ → ℝ → ℝ)
    (hxx : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2)) (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative (itoTimeShift f a) p.1 p.2) :=
  hxx.comp ((continuous_const.add continuous_fst).prodMk continuous_snd)

end Paper
