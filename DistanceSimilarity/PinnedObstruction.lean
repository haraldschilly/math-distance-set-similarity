import DistanceSimilarity.Statements

/-!
# Theorem B: pinned distance sets are not universal hosts for the dyadic sequence

Let `A ⊆ [0,1]` be a compact set of measure `> 1 - η` containing no affine copy of
`D = {2⁻ⁿ : n ≥ 1}` (the dyadic case of the Erdős similarity conjecture,
`DyadicAvoidanceStatement`). The radial set `K = {y ∈ ℝ^d : ‖y‖ ∈ A ∪ {0}}` is compact, has
positive volume (hence full Hausdorff dimension `d`), and its pinned distance set from the origin
is contained in `A ∪ {0}`, so it contains no affine copy of `D`. In contrast, the full distance
set `Δ(K)` contains an interval `[0, ε)` (Steinhaus), hence affine copies of `D`.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace DistanceSimilarity

lemma dyadicPoint_add (m n : ℕ) : dyadicPoint (m + n) = dyadicPoint m * dyadicPoint n := by
  simp [dyadicPoint, pow_add]

lemma dyadicPoint_injective : Function.Injective dyadicPoint :=
  pow_right_injective₀ (by norm_num) (by norm_num)

lemma dyadicPoint_pos (n : ℕ) : 0 < dyadicPoint n := by
  unfold dyadicPoint; positivity

lemma ContainsDyadicCopy.mono {P Q : Set ℝ} (h : ContainsDyadicCopy P) (hPQ : P ⊆ Q) :
    ContainsDyadicCopy Q := by
  obtain ⟨x, s, hs, hx⟩ := h
  exact ⟨x, s, hs, fun n hn => hPQ (hx n hn)⟩

/-- Adding the point `0` to a set that avoids every affine copy of `D` keeps this property:
a copy meets `0` at most once, and its tail after that point is again an affine copy of `D`. -/
theorem not_containsDyadicCopy_insert_zero {A : Set ℝ}
    (hA : ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x + s * dyadicPoint n ∉ A) :
    ¬ ContainsDyadicCopy (insert 0 A) := by
  rintro ⟨x, s, hs, hall⟩
  by_cases h0 : ∃ m : ℕ, x + s * dyadicPoint m = 0
  · obtain ⟨m, hm⟩ := h0
    obtain ⟨n, hn, hnA⟩ := hA x (s * dyadicPoint m) (mul_ne_zero hs (dyadicPoint_pos m).ne')
    rcases hall (m + n) (by omega) with hzero | hmem
    · have : dyadicPoint (m + n) = dyadicPoint m :=
        mul_left_cancel₀ hs (by linarith)
      have := dyadicPoint_injective this
      omega
    · exact hnA (by rwa [dyadicPoint_add, ← mul_assoc] at hmem)
  · push Not at h0
    obtain ⟨n, hn, hnA⟩ := hA x s hs
    rcases hall n hn with hzero | hmem
    · exact h0 n hzero
    · exact hnA hmem

/-- A subset of `ℝ^d` of positive volume has Hausdorff dimension `d`. -/
theorem dimH_eq_of_volume_pos {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : 0 < volume K) : dimH K = d := by
  apply le_antisymm
  · calc dimH K ≤ dimH (univ : Set (EuclideanSpace ℝ (Fin d))) := dimH_mono (subset_univ _)
      _ = d := by rw [Real.dimH_univ_eq_finrank, finrank_euclideanSpace_fin]
  · let e := EuclideanSpace.equiv (Fin d) ℝ
    rw [← e.dimH_image]
    have himage : e '' K = (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹' K := by
      ext v
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hv
        exact ⟨WithLp.toLp 2 v, hv, rfl⟩
    have hvol : volume (e '' K) = volume K := by
      rw [himage]
      exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).symm.measure_preimage_equiv K
    have hH : μH[((d : ℝ≥0) : ℝ)] (e '' K) ≠ 0 := by
      have h := hausdorffMeasure_pi_real (ι := Fin d)
      simp only [Fintype.card_fin] at h
      rw [NNReal.coe_natCast, h, hvol]
      exact hK.ne'
    simpa using le_dimH_of_hausdorffMeasure_ne_zero hH

/-- Polar coordinates: the radial set over a compact `A ⊆ [0,1]` of positive measure has positive
volume. -/
theorem volume_norm_preimage_pos {d : ℕ} (hd : 1 ≤ d) {A : Set ℝ} (hAc : IsCompact A)
    (hA01 : A ⊆ Icc 0 1) (hApos : 0 < volume A) :
    0 < volume ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) ⁻¹' A) := by
  have hAm : MeasurableSet A := hAc.measurableSet
  have hm : MeasurableSet ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) ⁻¹' A) :=
    measurable_norm hAm
  set f : ℝ → ℝ := A.indicator (fun _ => 1) with hf
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hpolar := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d))) f
  have hlhs : ∫ x : EuclideanSpace ℝ (Fin d), f ‖x‖ =
      volume.real ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) ⁻¹' A) := by
    rw [← integral_indicator_one hm]
    congr 1
  set g : ℝ → ℝ := A.indicator (fun y => y ^ (d - 1)) with hg
  have hrad : ∫ y in Ioi (0 : ℝ),
      y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1) • f y = ∫ y in Ioi (0 : ℝ), g y := by
    congr 1
    ext y
    by_cases hy : y ∈ A <;> simp [f, g, hy]
  have hgint : IntegrableOn g (Ioi 0) := by
    have : IntegrableOn (fun y : ℝ => y ^ (d - 1)) A :=
      (continuous_pow (d - 1)).continuousOn.integrableOn_compact hAc
    exact ((integrable_indicator_iff hAm).2 this).integrableOn
  have hgpos : 0 < ∫ y in Ioi (0 : ℝ), g y := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ hgint]
    · have hsub : A \ {0} ⊆ Function.support g ∩ Ioi 0 := by
        rintro y ⟨hyA, hy0⟩
        have hy : 0 < y := lt_of_le_of_ne (hA01 hyA).1 (Ne.symm hy0)
        refine ⟨?_, hy⟩
        rw [Function.mem_support, hg, Set.indicator_of_mem hyA]
        exact pow_ne_zero _ hy.ne'
      calc 0 < volume (A \ {0}) := by rwa [measure_sdiff_null (measure_singleton 0)]
        _ ≤ _ := measure_mono hsub
    · exact Eventually.of_forall fun y =>
        Set.indicator_nonneg (fun z hz => pow_nonneg (hA01 hz).1 _) y
  have hball : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hreal : 0 < volume.real ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) ⁻¹' A) := by
    rw [← hlhs, hpolar, hrad, finrank_euclideanSpace_fin, smul_eq_mul]
    exact nsmul_pos (mul_pos hball hgpos) (by omega)
  by_contra h0
  rw [not_lt, nonpos_iff_eq_zero] at h0
  simp [measureReal_def, h0] at hreal

/-- **Steinhaus contrast.** If `K ⊆ ℝ^d` (`d ≥ 1`) is compact of positive volume, then `Δ(K)`
contains an interval `[0, ε)`, hence an affine copy of the dyadic sequence. -/
theorem containsDyadicCopy_distSet_of_volume_pos {d : ℕ} (hd : 1 ≤ d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hKc : IsCompact K) (hK : 0 < volume K) :
    ContainsDyadicCopy (distSet K) := by
  have hst := Measure.sub_mem_nhds_zero_of_addHaar_pos_ne_top volume K hKc.measurableSet hK
    hKc.measure_lt_top.ne
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hst
  refine ⟨0, ε / 2, by positivity, fun n _ => ?_⟩
  have hdp : dyadicPoint n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set r := 0 + ε / 2 * dyadicPoint n with hr
  have hr0 : 0 ≤ r := by have := dyadicPoint_pos n; rw [hr]; positivity
  have hrε : r < ε := by
    rw [hr, zero_add]
    calc ε / 2 * dyadicPoint n ≤ ε / 2 * 1 := by gcongr
      _ < ε := by linarith
  set v : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, by omega⟩ r
  have hv : ‖v‖ = r := by simp [v, abs_of_nonneg hr0]
  have hvmem : v ∈ ball (0 : EuclideanSpace ℝ (Fin d)) ε := by
    rw [mem_ball, dist_zero_right, hv]; exact hrε
  obtain ⟨x, hx, y, hy, hxy⟩ := hball hvmem
  exact ⟨x, hx, y, hy, by simp only at hxy; rw [dist_eq_norm, hxy, hv]⟩

/-- **Theorem B.** Assume the dyadic case of the Erdős similarity conjecture. For every `d ≥ 1`
and `η ∈ (0,1)` there is a compact set `K` in the closed unit ball of `ℝ^d`, containing the origin,
of positive volume and full Hausdorff dimension `d`, such that the pinned distance set
`{‖y‖ : y ∈ K}` contains no nontrivial affine copy of `{2⁻ⁿ : n ≥ 1}`, while the full distance set
`Δ(K)` does contain one. -/
theorem pinned_dyadic_obstruction (hDy : DyadicAvoidanceStatement) {d : ℕ} (hd : 1 ≤ d)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ K : Set (EuclideanSpace ℝ (Fin d)),
      IsCompact K ∧ K ⊆ closedBall 0 1 ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ K ∧
      0 < volume K ∧ dimH K = d ∧
      ¬ ContainsDyadicCopy (pinnedDistSet 0 K) ∧ ContainsDyadicCopy (distSet K) := by
  obtain ⟨A, hA01, hAc, hAvol, hAavoid⟩ := hDy η hη0 hη1
  have hApos : 0 < volume A := zero_le.trans_lt hAvol
  set K := (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) ⁻¹' (insert 0 A) with hK
  have hKclosed : IsClosed K := (hAc.insert 0).isClosed.preimage continuous_norm
  have hKball : K ⊆ closedBall 0 1 := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    rcases hy with h | h
    · simp only at h; rw [h]; exact zero_le_one
    · exact (hA01 h).2
  have hKc : IsCompact K :=
    isCompact_of_isClosed_isBounded hKclosed (isBounded_closedBall.subset hKball)
  have hKpos : 0 < volume K :=
    (volume_norm_preimage_pos hd hAc hA01 hApos).trans_le
      (measure_mono (preimage_mono (subset_insert _ _)))
  refine ⟨K, hKc, hKball, by simp [hK], hKpos, dimH_eq_of_volume_pos hKpos, ?_,
    containsDyadicCopy_distSet_of_volume_pos hd hKc hKpos⟩
  intro hcopy
  apply not_containsDyadicCopy_insert_zero hAavoid
  refine hcopy.mono ?_
  rintro r ⟨y, hy, rfl⟩
  simpa [dist_zero_left, hK] using hy

end DistanceSimilarity
