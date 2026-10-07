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

/-- `P` contains a nontrivial affine copy `x + s·{qⁿ : n ≥ 1}` of the geometric sequence of
ratio `q`. For `q = 1/2` this is `ContainsDyadicCopy` (see `containsDyadicCopy_iff`). -/
def ContainsGeomCopy (q : ℝ) (P : Set ℝ) : Prop :=
  ∃ x s : ℝ, s ≠ 0 ∧ ∀ n : ℕ, 1 ≤ n → x + s * q ^ n ∈ P

/-- `P` contains a nontrivial affine copy `x + s·F` of the set `F`. -/
def ContainsAffineCopy (F P : Set ℝ) : Prop :=
  ∃ x s : ℝ, s ≠ 0 ∧ ∀ a ∈ F, x + s * a ∈ P

/-- The geometric case of the Erdős similarity conjecture for the ratio `q`: the same statement
as `DyadicAvoidanceStatement` with `2⁻ⁿ` replaced by `qⁿ`. For `q = 1/2` this *is*
`DyadicAvoidanceStatement` (see `dyadicAvoidance_iff`), which OpenAI proved in Lean. For other
`q ∈ (0,1)` it is claimed in OpenAI's preprint "The geometric case of the Erdős similarity
conjecture" (October 5, 2026), **without** a Lean proof. -/
def GeometricAvoidanceStatement (q : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ,
    E ⊆ Set.Icc (0 : ℝ) 1 ∧ IsCompact E ∧
    MeasureTheory.volume E > ENNReal.ofReal (1 - η) ∧
    ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x + s * q ^ n ∉ E

/-- The Mattila–Sjölin theorem (P. Mattila, P. Sjölin, *Regularity of distance measures and
sets*, Math. Nachr. 204 (1999), 157–162), compact case: if `dimH E > (d+1)/2` then the distance
set has nonempty interior. It is used only in `window_of_mattilaSjolin` (Remark 5.1 of the paper).
It is proved, with this exact statement, in the separate formalization
github.com/haraldschilly/math-mattila-sjolin (`MattilaSjolin.mattilaSjolin`);
`verify/Verify/MattilaSjolin.lean` checks this with the kernel. -/
def MattilaSjolinStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E →
    ((d : ℝ≥0∞) + 1) / 2 < dimH E →
      (interior {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}).Nonempty

theorem dyadicAvoidance_iff : DyadicAvoidanceStatement ↔ GeometricAvoidanceStatement 2⁻¹ :=
  Iff.rfl

theorem containsDyadicCopy_iff {P : Set ℝ} : ContainsDyadicCopy P ↔ ContainsGeomCopy 2⁻¹ P :=
  Iff.rfl

end DistanceSimilarity
