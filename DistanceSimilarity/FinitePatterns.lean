import DistanceSimilarity.Statements

/-!
# Theorem A: finite patterns in Falconer distance sets

If `E ⊆ ℝ^d` (`d ≥ 2`) is compact with `dimH E > d/2`, then for every finite `F ⊆ ℝ` and every
sufficiently small dilation `s`, the set of translations `x` with `x + s • F ⊆ Δ(E)` has positive
Lebesgue measure. In particular `Δ(E)` contains affine copies of `F` with arbitrarily small
dilations of either sign.

The only deep input is the Falconer distance theorem (`FalconerStatement`). The rest is the
classical Steinhaus-type argument: translation is continuous in measure.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal symmDiff

namespace DistanceSimilarity

/-- Translation `x ↦ x + c` as a continuous map depending continuously on `c`. -/
private noncomputable def translate (a : ℝ) : C(ℝ, C(ℝ, ℝ)) :=
  ContinuousMap.curry ⟨fun p : ℝ × ℝ => p.2 + p.1 * a, by fun_prop⟩

private lemma translate_apply (a s x : ℝ) : translate a s x = x + s * a := rfl

/-- **Steinhaus lemma for finite patterns.** A set of positive finite measure contains, for every
sufficiently small `s`, a positive-measure family of translates of `s • F`. -/
theorem eventually_volume_pattern_pos {S : Set ℝ} (hS : MeasurableSet S) (hfin : volume S ≠ ∞)
    (hpos : 0 < volume S) (F : Finset ℝ) :
    ∀ᶠ s in 𝓝 (0 : ℝ), 0 < volume {x : ℝ | ∀ a ∈ F, x + s * a ∈ S} := by
  -- For each `a`, the translate `S - s a` tends to `S` in measure as `s → 0`.
  have key : ∀ a ∈ F, Tendsto (fun s : ℝ => volume ((translate a s ⁻¹' S) ∆ S))
      (𝓝 0) (𝓝 0) := by
    intro a _
    have h0 : translate a 0 = ContinuousMap.id ℝ := by
      ext x; simp [translate_apply]
    have hmp : ∀ s, MeasurePreserving (translate a s) volume volume := fun s => by
      have hcoe : ⇑(translate a s) = fun x => x + s * a := rfl
      rw [hcoe]
      exact measurePreserving_add_right volume (s * a)
    have := tendsto_measure_symmDiff_preimage_nhds_zero (μ := volume) (ν := volume)
      ((translate a).continuous.tendsto 0) (Eventually.of_forall hmp) (hmp 0)
      hS.nullMeasurableSet hfin
    simpa [h0] using this
  have hsum : Tendsto (fun s : ℝ => ∑ a ∈ F, volume ((translate a s ⁻¹' S) ∆ S))
      (𝓝 0) (𝓝 0) := by
    simpa using tendsto_finsetSum F key
  filter_upwards [(tendsto_order.1 hsum).2 _ hpos] with s hs
  -- `S` is covered by the good set and the union of the defects `S \ (S - s a)`.
  have hcover : S ⊆ {x : ℝ | ∀ a ∈ F, x + s * a ∈ S} ∪
      ⋃ a ∈ F, (translate a s ⁻¹' S) ∆ S := by
    intro x hx
    by_cases h : ∀ a ∈ F, x + s * a ∈ S
    · exact Or.inl h
    · push Not at h
      obtain ⟨a, ha, hxa⟩ := h
      refine Or.inr (mem_iUnion₂.2 ⟨a, ha, Or.inr ⟨hx, ?_⟩⟩)
      simpa [translate_apply] using hxa
  have hle : volume S ≤ volume {x : ℝ | ∀ a ∈ F, x + s * a ∈ S} +
      ∑ a ∈ F, volume ((translate a s ⁻¹' S) ∆ S) :=
    (measure_mono hcover).trans <| (measure_union_le _ _).trans <|
      add_le_add le_rfl (measure_biUnion_finset_le _ _)
  by_contra hzero
  rw [not_lt, nonpos_iff_eq_zero] at hzero
  rw [hzero, zero_add] at hle
  exact absurd hs (not_lt.2 hle)

/-- The distance set of a compact set is compact. -/
theorem isCompact_distSet {X : Type*} [PseudoMetricSpace X] {E : Set X} (hE : IsCompact E) :
    IsCompact (distSet E) := by
  have : distSet E = (fun p : X × X => dist p.1 p.2) '' (E ×ˢ E) := by
    ext r; simp [distSet]
  rw [this]
  exact (hE.prod hE).image continuous_dist

/-- **Theorem A.** Finite patterns are universal in Falconer distance sets: for all sufficiently
small dilations `s` (of either sign), a positive-measure set of translations `x` satisfies
`x + s • F ⊆ Δ(E)`. -/
theorem finite_pattern_distSet (hFal : FalconerStatement) {d : ℕ} (hd : 2 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E) (hdim : (d : ℝ≥0∞) / 2 < dimH E)
    (F : Finset ℝ) :
    ∀ᶠ s in 𝓝 (0 : ℝ), 0 < volume {x : ℝ | ∀ a ∈ F, x + s * a ∈ distSet E} := by
  have hK := isCompact_distSet hE
  exact eventually_volume_pattern_pos hK.measurableSet hK.measure_lt_top.ne
    (hFal d hd E hE hdim) F

/-- **Theorem A, existence form.** For every `δ > 0`, `Δ(E)` contains affine copies `x + s • F` of
the finite set `F` with `0 < s < δ`, and also with `-δ < s < 0`. -/
theorem exists_finite_pattern_distSet (hFal : FalconerStatement) {d : ℕ} (hd : 2 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E) (hdim : (d : ℝ≥0∞) / 2 < dimH E)
    (F : Finset ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∃ x s : ℝ, 0 < s ∧ s < δ ∧ ∀ a ∈ F, x + s * a ∈ distSet E) ∧
    (∃ x s : ℝ, -δ < s ∧ s < 0 ∧ ∀ a ∈ F, x + s * a ∈ distSet E) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (finite_pattern_distSet hFal hd hE hdim F)
  have pick : ∀ s : ℝ, |s| < ε → ∃ x : ℝ, ∀ a ∈ F, x + s * a ∈ distSet E := fun s hs =>
    nonempty_of_measure_ne_zero (hball (by simpa [Real.dist_eq] using hs)).ne'
  set t := min ε δ / 2 with ht
  have ht0 : 0 < t := by positivity
  have htε : t < ε := by
    have := min_le_left ε δ; linarith [half_lt_self (lt_min hε hδ)]
  have htδ : t < δ := by
    have := min_le_right ε δ; linarith [half_lt_self (lt_min hε hδ)]
  obtain ⟨x, hx⟩ := pick t (by rwa [abs_of_pos ht0])
  obtain ⟨y, hy⟩ := pick (-t) (by rwa [abs_neg, abs_of_pos ht0])
  exact ⟨⟨x, t, ht0, htδ, hx⟩, ⟨y, -t, by linarith, by linarith, hy⟩⟩

/-- **Distances at every scale** (Section 1.2). If `dimH E > d/2`, then `Δ(E) ∩ [0, r]` has
positive measure for every `r > 0`: cover `E` by finitely many balls of radius `r/2`; one of the
pieces still has dimension `> d/2`, and its distances are at most `r`. -/
theorem volume_distSet_inter_Icc_pos (hFal : FalconerStatement) {d : ℕ} (hd : 2 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E) (hdim : (d : ℝ≥0∞) / 2 < dimH E)
    {r : ℝ} (hr : 0 < r) : 0 < volume (distSet E ∩ Icc 0 r) := by
  obtain ⟨t, -, hcover⟩ := hE.elim_nhds_subcover (fun x => Metric.closedBall x (r / 2))
    (fun x _ => Metric.closedBall_mem_nhds x (by positivity))
  have hEeq : E = ⋃ c ∈ t, E ∩ Metric.closedBall c (r / 2) := by
    ext y; constructor
    · intro hy
      obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 (hcover hy)
      exact mem_iUnion₂.2 ⟨c, hc, hy, hyc⟩
    · intro hy
      obtain ⟨c, _, hyc⟩ := mem_iUnion₂.1 hy
      exact hyc.1
  have hdimU : dimH E = ⨆ c ∈ (t : Set (EuclideanSpace ℝ (Fin d))),
      dimH (E ∩ Metric.closedBall c (r / 2)) := by
    conv_lhs => rw [hEeq]
    exact dimH_bUnion t.countable_toSet _
  rw [hdimU] at hdim
  obtain ⟨c, hc, hdimc⟩ : ∃ c ∈ (t : Set (EuclideanSpace ℝ (Fin d))),
      (d : ℝ≥0∞) / 2 < dimH (E ∩ Metric.closedBall c (r / 2)) := by
    by_contra h
    push Not at h
    exact absurd hdim (not_lt.2 (iSup₂_le h))
  have hcpt : IsCompact (E ∩ Metric.closedBall c (r / 2)) := hE.inter_right Metric.isClosed_closedBall
  refine (hFal d hd _ hcpt hdimc).trans_le (measure_mono ?_)
  rintro _ ⟨x, hx, y, hy, rfl⟩
  refine ⟨⟨x, hx.1, y, hy.1, rfl⟩, dist_nonneg, ?_⟩
  have := dist_triangle_right x y c
  have hx' := Metric.mem_closedBall.1 hx.2
  have hy' := Metric.mem_closedBall.1 hy.2
  linarith

/-- **Theorem A, planar form** (Remark 3.2). The set of pairs `(s, x)` with `x + s • F ⊆ Δ(E)` has
positive planar Lebesgue measure. -/
theorem volume_pattern_pairs_pos (hFal : FalconerStatement) {d : ℕ} (hd : 2 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : IsCompact E) (hdim : (d : ℝ≥0∞) / 2 < dimH E)
    (F : Finset ℝ) :
    0 < volume {p : ℝ × ℝ | ∀ a ∈ F, p.2 + p.1 * a ∈ distSet E} := by
  set S := {p : ℝ × ℝ | ∀ a ∈ F, p.2 + p.1 * a ∈ distSet E} with hS
  have hSc : IsClosed S := by
    have hSeq : S = ⋂ a ∈ (F : Set ℝ), (fun p : ℝ × ℝ => p.2 + p.1 * a) ⁻¹' distSet E := by
      ext p; simp [hS]
    rw [hSeq]
    exact isClosed_biInter fun a _ =>
      (isCompact_distSet hE).isClosed.preimage (by fun_prop)
  rw [Measure.volume_eq_prod, Measure.prod_apply hSc.measurableSet]
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (finite_pattern_distSet hFal hd hE hdim F)
  have hmeas : Measurable fun s : ℝ => volume (Prod.mk s ⁻¹' S) :=
    measurable_measure_prodMk_left hSc.measurableSet
  rw [lintegral_pos_iff_support hmeas]
  refine lt_of_lt_of_le ?_ (measure_mono (s := Metric.ball (0 : ℝ) ε) fun s hs => ?_)
  · exact Metric.measure_ball_pos _ _ hε
  · exact (hball hs).ne'

end DistanceSimilarity
