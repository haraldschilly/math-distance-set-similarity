import DistanceSimilarity.FinitePatterns
import DistanceSimilarity.PinnedObstruction

/-!
# Proposition C: where the question is open

* `distSet_containsAffineCopy_of_interior`, `distSet_containsGeomCopy_of_volume_pos`: if `Δ(E)`
  has nonempty interior (for instance if `E` has positive volume), it contains affine copies of every
  bounded set and of every geometric sequence.
* `counterexample_properties`: a counterexample to Question 1.1 with `dimH E > d/2` has a distance
  set of positive measure but empty interior, and `E` has volume zero.
* `window_of_mattilaSjolin` (Remark 5.1): if moreover the classical Mattila–Sjölin theorem is
  assumed (`MattilaSjolinStatement`, discharged in `verify/`), such a counterexample has
  `dimH E ≤ (d+1)/2`.
* `not_containsGeomCopy_pinnedDistSet_iff` (Lemma 6.1): the reformulation used in the open
  questions (Section 6): a pinned distance set avoids all copies iff every copy meets a radius whose sphere
  misses `E`.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace DistanceSimilarity

variable {d : ℕ}

/-- **Proposition C(i).** If `Δ(E)` has nonempty interior, it contains an affine copy of every
bounded set `F`. -/
theorem distSet_containsAffineCopy_of_interior {E : Set (EuclideanSpace ℝ (Fin d))}
    (hint : (interior (distSet E)).Nonempty) {F : Set ℝ} (hF : Bornology.IsBounded F) :
    ContainsAffineCopy F (distSet E) :=
  containsAffineCopy_of_interior_nonempty hint hF

/-- **Proposition C(ii).** If `E ⊆ ℝ^d` (`d ≥ 1`) is compact of positive volume, then `Δ(E)`
contains an affine copy of every bounded set `F` (and, below, of every geometric sequence). -/
theorem distSet_containsAffineCopy_of_volume_pos (hd : 1 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E) (hvol : 0 < volume E)
    {F : Set ℝ} (hF : Bornology.IsBounded F) : ContainsAffineCopy F (distSet E) :=
  distSet_containsAffineCopy_of_interior (interior_distSet_nonempty_of_volume_pos hd hE hvol) hF

theorem distSet_containsGeomCopy_of_volume_pos (hd : 1 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E) (hvol : 0 < volume E)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : ContainsGeomCopy q (distSet E) :=
  containsGeomCopy_of_interior_nonempty hq0 hq1 (interior_distSet_nonempty_of_volume_pos hd hE hvol)

/-- **Proposition C(iii).** Assume the Falconer theorem. If `E ⊆ ℝ^d` (`d ≥ 2`) is compact with
`dimH E > d/2` and `Δ(E)` contains no affine copy of `{qⁿ : n ≥ 1}` (`0 < q < 1`), then `Δ(E)` has
positive measure but empty interior, and `E` has volume zero. -/
theorem counterexample_properties (hFal : FalconerStatement) (hd : 2 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E) (hdim : (d : ℝ≥0∞) / 2 < dimH E)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hno : ¬ ContainsGeomCopy q (distSet E)) :
    0 < volume (distSet E) ∧ interior (distSet E) = ∅ ∧ volume E = 0 := by
  refine ⟨hFal d hd E hE hdim, ?_, ?_⟩
  · by_contra h
    exact hno (containsGeomCopy_of_interior_nonempty hq0 hq1 (nonempty_iff_ne_empty.2 h))
  · by_contra h
    exact hno (distSet_containsGeomCopy_of_volume_pos (by omega) hE (pos_iff_ne_zero.2 h) hq0 hq1)

/-- **Remark 5.1 (takes the Mattila–Sjölin theorem as an explicit hypothesis).**
Under `MattilaSjolinStatement`, a compact `E ⊆ ℝ^d` whose distance set avoids all affine copies of
`{qⁿ : n ≥ 1}` has `dimH E ≤ (d+1)/2`. So Question 1.1 is open only in the window
`d/2 < dimH E ≤ (d+1)/2`. -/
theorem window_of_mattilaSjolin (hMS : MattilaSjolinStatement) (hd : 2 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hno : ¬ ContainsGeomCopy q (distSet E)) :
    dimH E ≤ ((d : ℝ≥0∞) + 1) / 2 := by
  by_contra h
  exact hno (containsGeomCopy_of_interior_nonempty hq0 hq1 (hMS d hd E hE (not_le.1 h)))

/-- **Lemma 6.1 (reformulation used in the open questions).** The pinned distance set `Δ_p(E)`
contains no affine copy of `{qⁿ : n ≥ 1}` if and only if every such copy `x + s·{qⁿ}` contains a
radius `r` for which the sphere of radius `r` about `p` misses `E`. -/
theorem not_containsGeomCopy_pinnedDistSet_iff {q : ℝ} (p : EuclideanSpace ℝ (Fin d))
    (E : Set (EuclideanSpace ℝ (Fin d))) :
    ¬ ContainsGeomCopy q (pinnedDistSet p E) ↔
      ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ Disjoint (sphere p (x + s * q ^ n)) E := by
  have key : ∀ r : ℝ, r ∈ pinnedDistSet p E ↔ ¬ Disjoint (sphere p r) E := by
    intro r
    rw [not_disjoint_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, by rw [mem_sphere, dist_comm], hy⟩
    · rintro ⟨y, hys, hy⟩
      exact ⟨y, hy, by rw [mem_sphere] at hys; rw [dist_comm, hys]⟩
  simp only [ContainsGeomCopy, key, not_exists, not_and, not_forall, not_not, exists_prop]

end DistanceSimilarity
