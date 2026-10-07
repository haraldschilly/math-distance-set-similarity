import DistanceSimilarity.Patterns
import DistanceSimilarity.RadialVolume

/-!
# Theorem B: pinned distance sets are not universal hosts for geometric sequences

Let `0 < q < 1` and let `A ⊆ [0,1]` be a compact set of measure `> 1 - η` containing no affine
copy of `{qⁿ : n ≥ 1}` (`GeometricAvoidanceStatement q`; for `q = 1/2` this is OpenAI's formally
proved `DyadicAvoidanceStatement`). The radial set `K = {y ∈ ℝ^d : ‖y‖ ∈ A ∪ {0}}` is compact, has
volume `≥ (1-η)^d · vol(B)` (hence full Hausdorff dimension `d`), and its pinned distance set from
the origin is contained in `A ∪ {0}`, so it contains no affine copy of `{qⁿ}`. In contrast, the full
distance set `Δ(K)` and, for `d ≥ 2`, every other pinned distance set contain intervals, hence
affine copies of `{qⁿ}` (Theorems B and 4.6 of the paper).
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace DistanceSimilarity

/-- **Lemma 4.3.** A subset of `ℝ^d` of positive volume has Hausdorff dimension `d`. -/
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

/-- **Lemma 4.4 (Steinhaus).** If `K ⊆ ℝ^d` (`d ≥ 1`) is compact of positive volume, then `Δ(K)`
contains an interval `[0, ε)`; in particular it has nonempty interior. -/
theorem exists_Ico_subset_distSet {d : ℕ} (hd : 1 ≤ d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hKc : IsCompact K) (hK : 0 < volume K) :
    ∃ ε > 0, Ico 0 ε ⊆ distSet K := by
  have hst := Measure.sub_mem_nhds_zero_of_addHaar_pos_ne_top volume K hKc.measurableSet hK
    hKc.measure_lt_top.ne
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hst
  refine ⟨ε, hε, fun r hr => ?_⟩
  set v : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, by omega⟩ r
  have hv : ‖v‖ = r := by simp [v, abs_of_nonneg hr.1]
  have hvmem : v ∈ ball (0 : EuclideanSpace ℝ (Fin d)) ε := by
    rw [mem_ball, dist_zero_right, hv]; exact hr.2
  obtain ⟨x, hx, y, hy, hxy⟩ := hball hvmem
  exact ⟨x, hx, y, hy, by simp only at hxy; rw [dist_eq_norm, hxy, hv]⟩

theorem interior_distSet_nonempty_of_volume_pos {d : ℕ} (hd : 1 ≤ d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hKc : IsCompact K) (hK : 0 < volume K) :
    (interior (distSet K)).Nonempty := by
  obtain ⟨ε, hε, hsub⟩ := exists_Ico_subset_distSet hd hKc hK
  exact ⟨ε / 2, interior_mono (Ioo_subset_Ico_self.trans hsub)
    (by rw [interior_Ioo]; constructor <;> linarith)⟩

/-- **Lemma 4.5 (every other pin sees an interval).** If `d ≥ 2`, `p ≠ 0` and `K` contains the sphere of
radius `ρ > 0` about the origin, then `Δ_p(K) ⊇ [|‖p‖ - ρ|, ‖p‖ + ρ]`. -/
theorem Icc_subset_pinnedDistSet {d : ℕ} (hd : 2 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}
    {ρ : ℝ} (hρ : 0 < ρ) (hS : sphere (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ K)
    {p : EuclideanSpace ℝ (Fin d)} (hp : p ≠ 0) :
    Icc |‖p‖ - ρ| (‖p‖ + ρ) ⊆ pinnedDistSet p K := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin d)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast hd
  have hconn := ((isConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin d)) hρ.le).image
    (fun y => dist p y) (continuous_const.dist continuous_id).continuousOn).isPreconnected
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp
  set u : EuclideanSpace ℝ (Fin d) := (ρ / ‖p‖) • p with hu
  have hu_mem : u ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) ρ := by
    rw [mem_sphere_zero_iff_norm, hu, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      div_mul_cancel₀ _ hpn.ne']
  have hneg_mem : -u ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) ρ := by
    rwa [mem_sphere_zero_iff_norm, norm_neg, ← mem_sphere_zero_iff_norm]
  have hdist_u : dist p u = |‖p‖ - ρ| := by
    rw [dist_eq_norm, hu, show p - (ρ / ‖p‖) • p = (1 - ρ / ‖p‖) • p by
      rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs, ← abs_of_pos hpn, ← abs_mul,
      abs_of_pos hpn, sub_mul, one_mul, div_mul_cancel₀ _ hpn.ne']
  have hdist_neg : dist p (-u) = ‖p‖ + ρ := by
    rw [dist_eq_norm, sub_neg_eq_add, hu, show p + (ρ / ‖p‖) • p = (1 + ρ / ‖p‖) • p by
      rw [add_smul, one_smul], norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), add_mul,
      one_mul, div_mul_cancel₀ _ hpn.ne']
  intro r hr
  obtain ⟨y, hy, rfl⟩ := hconn.Icc_subset ⟨u, hu_mem, hdist_u⟩ ⟨-u, hneg_mem, hdist_neg⟩ hr
  exact ⟨y, hS hy, rfl⟩

/-- **Theorem 4.6 (Theorem B, general ratio).** Assume the geometric case of the Erdős similarity conjecture
for the ratio `q ∈ (0,1)`. For every `d ≥ 1` and `η ∈ (0,1)` there is a compact set `K` in the closed
unit ball of `ℝ^d`, containing the origin, of volume at least `(1-η)^d · vol(B(0,1))` and full
Hausdorff dimension `d`, such that the pinned distance set `{‖y‖ : y ∈ K}` contains no nontrivial
affine copy of `{qⁿ : n ≥ 1}`, while the full distance set `Δ(K)` does contain one, and for `d ≥ 2`
every pinned distance set `Δ_p(K)` with `p ≠ 0` contains a nondegenerate interval, hence a copy. -/
theorem pinned_geometric_obstruction {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hG : GeometricAvoidanceStatement q) {d : ℕ} (hd : 1 ≤ d)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ K : Set (EuclideanSpace ℝ (Fin d)),
      IsCompact K ∧ K ⊆ closedBall 0 1 ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ K ∧
      ENNReal.ofReal ((1 - η) ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ volume K ∧
      0 < volume K ∧ dimH K = d ∧
      ¬ ContainsGeomCopy q (pinnedDistSet 0 K) ∧ ContainsGeomCopy q (distSet K) ∧
      (2 ≤ d → ∀ p, p ≠ 0 → (∃ a b : ℝ, a < b ∧ Icc a b ⊆ pinnedDistSet p K) ∧
        ContainsGeomCopy q (pinnedDistSet p K)) := by
  obtain ⟨A, hA01, hAc, hAvol, hAavoid⟩ := hG η hη0 hη1
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
  have hAfin : volume A ≠ ∞ := ((measure_mono hA01).trans_lt measure_Icc_lt_top).ne
  have hAreal : 1 - η < volume.real A :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) hAfin).1 hAvol
  have hKge : ENNReal.ofReal ((1 - η) ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      volume K := by
    refine le_trans ?_ ((volume_norm_preimage_ge hd hAc hA01).trans
      (measure_mono (preimage_mono (subset_insert _ _))))
    gcongr
  have hKpos : 0 < volume K := by
    refine lt_of_lt_of_le ?_ hKge
    refine ENNReal.mul_pos ?_ (measure_ball_pos _ _ one_pos).ne'
    exact (ENNReal.ofReal_pos.2 (pow_pos (by linarith) d)).ne'
  refine ⟨K, hKc, hKball, by simp [hK], hKge, hKpos, dimH_eq_of_volume_pos hKpos, ?_,
    containsGeomCopy_of_interior_nonempty hq0 hq1
      (interior_distSet_nonempty_of_volume_pos hd hKc hKpos), ?_⟩
  rotate_left
  · intro hd2 p hp
    obtain ⟨ρ, hρA, hρ0⟩ : (A \ {0}).Nonempty :=
      nonempty_of_measure_ne_zero (by rw [measure_sdiff_null Real.volume_singleton]; exact hApos.ne')
    have hρ : 0 < ρ := lt_of_le_of_ne (hA01 hρA).1 (Ne.symm hρ0)
    have hS : sphere (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ K := fun y hy => by
      rw [mem_sphere_zero_iff_norm] at hy
      show ‖y‖ ∈ insert 0 A
      rw [hy]; exact Or.inr hρA
    have hlt : |‖p‖ - ρ| < ‖p‖ + ρ := by
      have := norm_pos_iff.2 hp
      rw [abs_lt]; constructor <;> linarith
    have hIcc := Icc_subset_pinnedDistSet hd2 hρ hS hp
    exact ⟨⟨_, _, hlt, hIcc⟩, (containsGeomCopy_Icc hq0 hq1 hlt).mono hIcc⟩
  intro hcopy
  apply not_containsGeomCopy_insert_zero hq0 hq1 hAavoid
  refine hcopy.mono ?_
  rintro r ⟨y, hy, rfl⟩
  simpa [dist_zero_left, hK] using hy

/-- **Theorem B.** Assume the dyadic case of the Erdős similarity conjecture. For every `d ≥ 1`
and `η ∈ (0,1)` there is a compact set `K` in the closed unit ball of `ℝ^d`, containing the origin,
of volume at least `(1-η)^d · vol(B(0,1))` and full Hausdorff dimension `d`, such that the pinned
distance set `{‖y‖ : y ∈ K}` contains no nontrivial affine copy of `{2⁻ⁿ : n ≥ 1}`, while the full
distance set `Δ(K)` does contain one, and for `d ≥ 2` every `Δ_p(K)` with `p ≠ 0` contains a
nondegenerate interval, hence a copy. -/
theorem pinned_dyadic_obstruction (hDy : DyadicAvoidanceStatement) {d : ℕ} (hd : 1 ≤ d)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ K : Set (EuclideanSpace ℝ (Fin d)),
      IsCompact K ∧ K ⊆ closedBall 0 1 ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ K ∧
      ENNReal.ofReal ((1 - η) ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ volume K ∧
      0 < volume K ∧ dimH K = d ∧
      ¬ ContainsDyadicCopy (pinnedDistSet 0 K) ∧ ContainsDyadicCopy (distSet K) ∧
      (2 ≤ d → ∀ p, p ≠ 0 → (∃ a b : ℝ, a < b ∧ Icc a b ⊆ pinnedDistSet p K) ∧
        ContainsDyadicCopy (pinnedDistSet p K)) :=
  pinned_geometric_obstruction (by norm_num) (by norm_num) hDy hd hη0 hη1

end DistanceSimilarity
