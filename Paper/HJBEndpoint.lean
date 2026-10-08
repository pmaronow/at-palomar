module

public import Paper.HJBVerification

@[expose] public section

/-! # Removing the Cole--Hopf terminal time cap

The random endpoint is held fixed. Unit spatial Lipschitz bounds and compact
time continuity provide an actual integrable domination for the potential.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace Paper
open SpinGlass SpinGlass.Targets

theorem hjbTerminalCap_mem (a b c : ℝ) (hc : c ∈ Ioo a b) :
    hjbTimeCap c ((b - c) / 2) b ∈ Icc a b := by
  have hδ : 0 < (b - c) / 2 := by linarith [hc.2]
  have hlo := hjbTimeCap_ge c hδ hc.2.le
  have hhi := hjbTimeCap_lt c hδ b
  exact ⟨hc.1.le.trans hlo, by linarith⟩

theorem tendsto_hjbTerminalCap (b : ℝ) :
    Tendsto (fun c => hjbTimeCap c ((b - c) / 2) b) (𝓝[<] b) (𝓝 b) := by
  have hi : Tendsto (fun c : ℝ => c) (𝓝[<] b) (𝓝 b) := nhdsWithin_le_nhds
  have hu : Tendsto (fun c : ℝ => c + (b - c) / 2) (𝓝[<] b) (𝓝 b) := by
    convert hi.add ((tendsto_const_nhds.sub hi).div_const 2) using 1 <;> simp
  apply hi.squeeze' hu
  · filter_upwards [self_mem_nhdsWithin] with c hc
    change c < b at hc
    exact hjbTimeCap_ge c (by linarith : 0 < (b - c) / 2) hc.le
  · filter_upwards [self_mem_nhdsWithin] with c hc
    change c < b at hc
    exact (hjbTimeCap_lt c (by linarith : 0 < (b - c) / 2) b).le

set_option maxHeartbeats 600000 in
/-- Actual absolute-integral terminal convergence for every integrable
random endpoint; no convergence of the state process is assumed. -/
theorem tendsto_integral_parisiSlab_terminalCap
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) (m : ℝ)
    (hm : m ∈ Icc (0 : ℝ) 1) (a b : ℝ) (hab : a < b)
    (Y : Ω → ℝ) (hY : Integrable Y P) :
    Tendsto (fun c => ∫ ω, parisiSlabPotential s β j m b
      (hjbTimeCap c ((b - c) / 2) b) (Y ω) ∂P) (𝓝[<] b)
      (𝓝 (∫ ω, parisiSlabPotential s β j m b b (Y ω) ∂P)) := by
  have hU := (continuous_parisiSlab s β j hm.1 b).1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hU.comp (continuous_id.prodMk continuous_const)).continuousOn :
      ContinuousOn (fun t => parisiSlabPotential s β j m b t 0) (Icc a b))
  have hmeas : ∀ᶠ c in 𝓝[<] b, AEStronglyMeasurable
      (fun ω => parisiSlabPotential s β j m b
        (hjbTimeCap c ((b - c) / 2) b) (Y ω)) P := by
    exact .of_forall fun c => hU.comp_aestronglyMeasurable
      (aestronglyMeasurable_const.prodMk hY.aestronglyMeasurable)
  have hbound : ∀ᶠ c in 𝓝[<] b, ∀ᵐ ω ∂P,
      ‖parisiSlabPotential s β j m b (hjbTimeCap c ((b - c) / 2) b) (Y ω)‖ ≤
        C + ‖Y ω‖ := by
    filter_upwards [Ioo_mem_nhdsLT hab] with c hc
    exact .of_forall fun ω => (parisiSlabPotential_norm_le s β j hm b _ (Y ω)).trans
      (add_le_add (hC _ (hjbTerminalCap_mem a b c hc)) (le_refl _))
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun c => parisiSlabPotential s β j m b (hjbTimeCap c ((b - c) / 2) b) (Y ω))
      (𝓝[<] b) (𝓝 (parisiSlabPotential s β j m b b (Y ω))) := by
    refine .of_forall fun ω => ?_
    have hcont : ContinuousAt (fun p : ℝ × ℝ => parisiSlabPotential s β j m b p.1 p.2)
        (b, Y ω) := hU.continuousAt
    exact hcont.tendsto.comp ((tendsto_hjbTerminalCap b).prodMk_nhds
      (tendsto_const_nhds (x := Y ω)))
  exact tendsto_integral_filter_of_dominated_convergence (fun ω => C + ‖Y ω‖)
    hmeas hbound ((integrable_const C).add hY.norm) hlim

theorem tendsto_integral_parisiSlab_terminalCap_Ioo
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) (m : ℝ)
    (hm : m ∈ Icc (0 : ℝ) 1) (a b : ℝ) (hab : a < b)
    (Y : Ω → ℝ) (hY : Integrable Y P) :
    Tendsto (fun c => ∫ ω, parisiSlabPotential s β j m b
      (hjbTimeCap c ((b - c) / 2) b) (Y ω) ∂P) (𝓝[Ioo a b] b)
      (𝓝 (∫ ω, parisiSlabPotential s β j m b b (Y ω) ∂P)) :=
  (tendsto_integral_parisiSlab_terminalCap s β j m hm a b hab Y hY).mono_left
    (nhdsWithin_mono _ (fun _ h => h.2))

end Paper
