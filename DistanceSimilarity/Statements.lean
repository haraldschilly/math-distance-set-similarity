import Mathlib

/-!
# Statements imported from the OpenAI math release

We do not reprove the two deep inputs. Instead their statements are recorded here as
propositions, copied verbatim (up to the name of the bound proposition) from the comparator
challenges of `github.com/openai/math`, commit `adc7f1241`:

* `lean/ComparatorChallenges/FalconerAllDimensions.lean` (`OAI.Falconer.falconer_distance_conjecture`)
* `lean/ComparatorChallenges/DyadicAvoidance.lean` (`OAI.Problem310.dyadic_affine_avoidance`)

Both are proved in the OAI Lean library (same toolchain `v4.34.1`, same Mathlib commit as this
project). Every theorem in this repository takes them as explicit hypotheses, so `#print axioms`
shows no dependence beyond the standard axioms.
-/

open MeasureTheory Set
open scoped ENNReal

namespace DistanceSimilarity

/-- The dyadic sequence `n ↦ 2⁻ⁿ` (same definition as `OAI.Problem310.dyadicPoint`). -/
noncomputable def dyadicPoint (n : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ n

/-- The Falconer distance conjecture in every dimension `d ≥ 2`
(statement of `OAI.Falconer.falconer_distance_conjecture`). -/
def FalconerStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E →
    (d : ℝ≥0∞) / 2 < dimH E →
      0 < volume {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

/-- The dyadic case of the Erdős similarity conjecture
(statement of `OAI.Problem310.dyadic_affine_avoidance`). -/
def DyadicAvoidanceStatement : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ,
    E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧
    MeasureTheory.volume E > ENNReal.ofReal (1 - η) ∧
    ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧
      x + s * dyadicPoint n ∉ E

/-- The distance set `Δ(E) = {‖x - y‖ : x, y ∈ E}`. -/
def distSet {X : Type*} [PseudoMetricSpace X] (E : Set X) : Set ℝ :=
  {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

/-- The pinned distance set `Δ_p(E) = {‖p - y‖ : y ∈ E}`. -/
def pinnedDistSet {X : Type*} [PseudoMetricSpace X] (p : X) (E : Set X) : Set ℝ :=
  {r : ℝ | ∃ y ∈ E, dist p y = r}

/-- `P` contains a nontrivial affine copy `x + s·{2⁻ⁿ : n ≥ 1}` of the dyadic sequence. -/
def ContainsDyadicCopy (P : Set ℝ) : Prop :=
  ∃ x s : ℝ, s ≠ 0 ∧ ∀ n : ℕ, 1 ≤ n → x + s * dyadicPoint n ∈ P

end DistanceSimilarity
