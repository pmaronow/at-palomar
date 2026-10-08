module

public import Targets.MixedReplicaTrace
public import Targets.MixedReplicaAverage

@[expose] public section

/-!
# Actual mixed moments under the disorder average

The finite moment notation is tied to the already constructed split law.
Its unit bound supplies integrability, so the actual SK trace can be averaged
without additional assumptions about replica observables.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ} {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- A finite kernel moment of the genuine disorder-averaged mixed split law. -/
noncomputable def averagedMixedReplicaMoment (Z : Ω → EnergySpace n)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l r : ℕ) (u : ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  ∑ p, ∑ q, averagedMixedConstrainedReplica Z u mode m v l r x y p q * K p q

theorem integrable_mixedReplicaMoment {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    Integrable (fun ω => mixedReplicaMoment mode m v l r (Z ω) u K x y) := by
  exact integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
    (integrable_mixedConstrainedReplica hZ u mode m v hm hv l r x y p q).mul_const (K p q)

theorem integral_mixedReplicaMoment {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    (∫ ω, mixedReplicaMoment mode m v l r (Z ω) u K x y) =
      averagedMixedReplicaMoment Z mode m v l r u K x y :=
  averagedMixedConstrainedReplica_moment hZ u mode m v hm hv l r x y K

/-- Integrability of the genuine contracted SK Hessian, including zero field
variances, follows from finite moments of the actual bounded split law. -/
theorem integrable_mixedConstrainedSecond_SK_trace
    (hn : 0 < n) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (j : ℕ) (x y : Fin n → ℝ) :
    Integrable (fun ω => ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      mixedConstrainedSecond mode m v j (Z ω) (sk.hU.w i) (sk.hU.w i) u x y) := by
  simp_rw [mixedConstrainedSecond_SK_trace hn β h sk _ u mode m v hm hv j x y]
  apply Integrable.const_mul
  apply Integrable.add
  · exact (integrable_const _).sub
      (integrable_mixedReplicaMoment hZ u mode m v hm hv 0 j _ x y)
  · exact integrable_finsetSum _ fun l _ => ((integrable_mixedReplicaMoment hZ u mode m v hm hv
      l (j - l) _ x y).sub (integrable_mixedReplicaMoment hZ u mode m v hm hv
        (l + 1) (j - (l + 1)) _ x y)).const_mul (m l)

/-- The original SK spectral trace, averaged under the actual mixed law.
The disorder input may be any measurable function; the original SK disorder
is used only to supply its exact spectral covariance. -/
theorem integral_mixedConstrainedSecond_SK_trace
    (hn : 0 < n) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (j : ℕ) (x y : Fin n → ℝ) :
    (∫ ω, ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      mixedConstrainedSecond mode m v j (Z ω) (sk.hU.w i) (sk.hU.w i) u x y) =
      n * (β ^ 2 * (1 + u ^ 2) -
        averagedMixedReplicaMoment Z mode m v 0 j u
          (fun p q => pairSKCovariance β p.1 q.1) x y +
        ∑ l : Fin j, m l * (
          averagedMixedReplicaMoment Z mode m v l (j - l) u
            (fun p q => pairSKCovariance β p.1 q.1) x y -
          averagedMixedReplicaMoment Z mode m v (l + 1) (j - (l + 1)) u
            (fun p q => pairSKCovariance β p.1 q.1) x y)) := by
  let K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ :=
    fun p q => pairSKCovariance β p.1 q.1
  have hi (l r : ℕ) := integrable_mixedReplicaMoment hZ u mode m v hm hv l r K x y
  have hs : Integrable (fun ω => ∑ l : Fin j, m l * (
      mixedReplicaMoment mode m v l (j - l) (Z ω) u K x y -
      mixedReplicaMoment mode m v (l + 1) (j - (l + 1)) (Z ω) u K x y)) :=
    integrable_finsetSum _ (fun l _ => ((hi l (j - l)).sub
      (hi (l + 1) (j - (l + 1)))).const_mul (m l))
  simp_rw [mixedConstrainedSecond_SK_trace hn β h sk _ u mode m v hm hv j x y]
  have hlin := integral_add ((integrable_const (β ^ 2 * (1 + u ^ 2))).sub (hi 0 j)) hs
  simp only [Pi.sub_apply, K] at hlin
  rw [integral_const_mul, hlin,
    integral_sub (integrable_const (β ^ 2 * (1 + u ^ 2))) (hi 0 j), integral_const,
    probReal_univ, smul_eq_mul, one_mul,
    integral_mixedReplicaMoment hZ u mode m v hm hv 0 j _ x y]
  congr 2
  have hsum := integral_finsetSum (Finset.univ : Finset (Fin j)) (fun l _ => ((hi l (j - l)).sub
      (hi (l + 1) (j - (l + 1)))).const_mul (m l))
  simp only [Pi.sub_apply, K] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_const_mul, integral_sub (hi l (j - l)) (hi (l + 1) (j - (l + 1))),
    integral_mixedReplicaMoment hZ u mode m v hm hv,
    integral_mixedReplicaMoment hZ u mode m v hm hv]

end SpinGlass.Targets
