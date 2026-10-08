module

public import Paper.GaussianPositivity
public import Paper.ATCoordinates

@[expose] public section

/-! # Strict Gaussian mean monotonicity

The field derivative and the actual positive odd Gaussian moment strengthen
Proposition 5.3's mean comparison to strict monotonicity at positive variance.
-/

namespace Paper

 theorem hasDerivAt_overlapTime_field (h t : ℝ) :
    HasDerivAt (fun a => overlapMap (Real.sqrt t) a 1) (2 * gaussianU h t) h := by
  convert (hasDerivAt_gaussianA_field h t).const_sub 1 using 1
  · ext a
    have he := gaussianA_add_overlap_time a t
    linarith
  · ring

 theorem overlapTime_strictMonoOn_field (t : ℝ) (ht : 0 < t) :
    StrictMonoOn (fun h => overlapMap (Real.sqrt t) h 1) (Set.Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro h _
    exact (hasDerivAt_overlapTime_field h t).continuousAt.continuousWithinAt
  · intro h hh
    have hhpos : 0 < h := by simpa only [interior_Ici, Set.mem_Ioi] using hh
    rw [(hasDerivAt_overlapTime_field h t).deriv]
    exact mul_pos (by norm_num) (gaussianU_pos h t hhpos ht)

end Paper
