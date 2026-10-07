import DistanceSimilarity
import Verify.Dyadic
import Verify.Falconer
import Verify.MattilaSjolin

/-!
# Unconditional results

The hypotheses `FalconerStatement` and `DyadicAvoidanceStatement` of the main library are
discharged by OpenAI's formal proofs (`Verify.Falconer`, `Verify.Dyadic`), and
`MattilaSjolinStatement` by the Mattila–Sjölin formalization (`Verify.MattilaSjolin`). The results
below therefore depend on nothing but Lean's standard axioms. (`pinned_geometric_obstruction` for
`q ≠ 1/2` keeps its hypothesis: OpenAI's geometric case has no Lean proof.)
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace DistanceSimilarity.Unconditional

theorem volume_distSet_inter_Icc_pos {d : ℕ} (hd : 2 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E) (hdim : (d : ℝ≥0∞) / 2 < dimH E)
    {r : ℝ} (hr : 0 < r) : 0 < volume (distSet E ∩ Icc 0 r) :=
  DistanceSimilarity.volume_distSet_inter_Icc_pos falconer_holds hd hE hdim hr

theorem finite_pattern_distSet {d : ℕ} (hd : 2 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E) (hdim : (d : ℝ≥0∞) / 2 < dimH E)
    (F : Finset ℝ) :
    ∀ᶠ s in 𝓝 (0 : ℝ), 0 < volume {x : ℝ | ∀ a ∈ F, x + s * a ∈ distSet E} :=
  DistanceSimilarity.finite_pattern_distSet falconer_holds hd hE hdim F

theorem volume_pattern_pairs_pos {d : ℕ} (hd : 2 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E) (hdim : (d : ℝ≥0∞) / 2 < dimH E)
    (F : Finset ℝ) :
    0 < volume {p : ℝ × ℝ | ∀ a ∈ F, p.2 + p.1 * a ∈ distSet E} :=
  DistanceSimilarity.volume_pattern_pairs_pos falconer_holds hd hE hdim F

theorem exists_dyadicFree_pos_every_scale :
    ∃ S : Set ℝ, IsCompact S ∧ S ⊆ Icc 0 1 ∧ (0 : ℝ) ∈ S ∧
      (∀ r : ℝ, 0 < r → 0 < volume (S ∩ Icc 0 r)) ∧ ¬ ContainsDyadicCopy S :=
  DistanceSimilarity.exists_dyadicFree_pos_every_scale dyadicAvoidance_holds

theorem pinned_dyadic_obstruction {d : ℕ} (hd : 1 ≤ d) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ K : Set (EuclideanSpace ℝ (Fin d)),
      IsCompact K ∧ K ⊆ closedBall 0 1 ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ K ∧
      ENNReal.ofReal ((1 - η) ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ volume K ∧
      0 < volume K ∧ dimH K = d ∧
      ¬ ContainsDyadicCopy (pinnedDistSet 0 K) ∧ ContainsDyadicCopy (distSet K) ∧
      (2 ≤ d → ∀ p, p ≠ 0 → (∃ a b : ℝ, a < b ∧ Icc a b ⊆ pinnedDistSet p K) ∧
        ContainsDyadicCopy (pinnedDistSet p K)) :=
  DistanceSimilarity.pinned_dyadic_obstruction dyadicAvoidance_holds hd hη0 hη1

theorem counterexample_properties {d : ℕ} (hd : 2 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E) (hdim : (d : ℝ≥0∞) / 2 < dimH E)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hno : ¬ ContainsGeomCopy q (distSet E)) :
    0 < volume (distSet E) ∧ interior (distSet E) = ∅ ∧ volume E = 0 :=
  DistanceSimilarity.counterexample_properties falconer_holds hd hE hdim hq0 hq1 hno

/-- Remark 5.1: a compact set whose distance set avoids every affine copy of `{qⁿ : n ≥ 1}` has
`dimH E ≤ (d+1)/2`. -/
theorem window_of_mattilaSjolin {d : ℕ} (hd : 2 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hno : ¬ ContainsGeomCopy q (distSet E)) :
    dimH E ≤ ((d : ℝ≥0∞) + 1) / 2 :=
  DistanceSimilarity.window_of_mattilaSjolin mattilaSjolin_holds hd hE hq0 hq1 hno

end DistanceSimilarity.Unconditional

#print axioms DistanceSimilarity.Unconditional.volume_distSet_inter_Icc_pos
#print axioms DistanceSimilarity.Unconditional.finite_pattern_distSet
#print axioms DistanceSimilarity.Unconditional.volume_pattern_pairs_pos
#print axioms DistanceSimilarity.Unconditional.exists_dyadicFree_pos_every_scale
#print axioms DistanceSimilarity.Unconditional.pinned_dyadic_obstruction
#print axioms DistanceSimilarity.Unconditional.counterexample_properties
#print axioms DistanceSimilarity.Unconditional.window_of_mattilaSjolin
