import DistanceSimilarity
import Verify.Dyadic
import Verify.Falconer

/-!
# Unconditional Theorems A and B

The hypotheses of the main library are discharged by OpenAI's formal proofs
(`Verify.Dyadic`, `Verify.Falconer`).
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal

namespace DistanceSimilarity

theorem finite_pattern_distSet' {d : ℕ} (hd : 2 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E) (hdim : (d : ℝ≥0∞) / 2 < dimH E)
    (F : Finset ℝ) :
    ∀ᶠ s in 𝓝 (0 : ℝ), 0 < volume {x : ℝ | ∀ a ∈ F, x + s * a ∈ distSet E} :=
  finite_pattern_distSet falconer_holds hd hE hdim F

theorem pinned_dyadic_obstruction' {d : ℕ} (hd : 1 ≤ d) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ K : Set (EuclideanSpace ℝ (Fin d)),
      IsCompact K ∧ K ⊆ closedBall 0 1 ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ K ∧
      ENNReal.ofReal ((1 - η) ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ volume K ∧
      0 < volume K ∧ dimH K = d ∧
      ¬ ContainsDyadicCopy (pinnedDistSet 0 K) ∧ ContainsDyadicCopy (distSet K) ∧
      (2 ≤ d → ∀ p, p ≠ 0 → ContainsDyadicCopy (pinnedDistSet p K)) :=
  pinned_dyadic_obstruction dyadicAvoidance_holds hd hη0 hη1

end DistanceSimilarity

#print axioms DistanceSimilarity.finite_pattern_distSet'
#print axioms DistanceSimilarity.pinned_dyadic_obstruction'
