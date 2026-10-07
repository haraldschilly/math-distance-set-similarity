import DistanceSimilarity.Statements
import DistanceSimilarity.RadialVolume

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

/-- A nondegenerate closed interval contains an affine copy of the dyadic sequence. -/
theorem containsDyadicCopy_Icc {a b : ℝ} (hab : a < b) : ContainsDyadicCopy (Icc a b) := by
  refine ⟨a, b - a, (sub_pos.2 hab).ne', fun n _ => ⟨?_, ?_⟩⟩
  · have := dyadicPoint_pos n
    nlinarith
  · have h1 : dyadicPoint n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith

/-- **Every other pin sees an interval.** If `d ≥ 2`, `p ≠ 0` and `K` contains the sphere of
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

/-- **Theorem B.** Assume the dyadic case of the Erdős similarity conjecture. For every `d ≥ 1`
and `η ∈ (0,1)` there is a compact set `K` in the closed unit ball of `ℝ^d`, containing the origin,
of positive volume and full Hausdorff dimension `d`, such that the pinned distance set
`{‖y‖ : y ∈ K}` contains no nontrivial affine copy of `{2⁻ⁿ : n ≥ 1}`, while the full distance set
`Δ(K)` does contain one. -/
theorem pinned_dyadic_obstruction (hDy : DyadicAvoidanceStatement) {d : ℕ} (hd : 1 ≤ d)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ K : Set (EuclideanSpace ℝ (Fin d)),
      IsCompact K ∧ K ⊆ closedBall 0 1 ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ K ∧
      ENNReal.ofReal ((1 - η) ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ volume K ∧
      0 < volume K ∧ dimH K = d ∧
      ¬ ContainsDyadicCopy (pinnedDistSet 0 K) ∧ ContainsDyadicCopy (distSet K) ∧
      (2 ≤ d → ∀ p, p ≠ 0 → ContainsDyadicCopy (pinnedDistSet p K)) := by
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
    containsDyadicCopy_distSet_of_volume_pos hd hKc hKpos, ?_⟩
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
    exact (containsDyadicCopy_Icc hlt).mono (Icc_subset_pinnedDistSet hd2 hρ hS hp)
  intro hcopy
  apply not_containsDyadicCopy_insert_zero hAavoid
  refine hcopy.mono ?_
  rintro r ⟨y, hy, rfl⟩
  simpa [dist_zero_left, hK] using hy

end DistanceSimilarity
