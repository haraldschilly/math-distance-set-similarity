import DistanceSimilarity.Statements

/-!
# Positive measure at every scale does not force a dyadic copy

By Lemma 3.3 of the paper (`volume_distSet_inter_Icc_pos`), a Falconer distance set `Δ(E)` has
positive measure in every interval `[0, r]`. This file shows that this property alone does not
force an affine copy of `{2⁻ⁿ : n ≥ 1}` (Proposition 3.4 of the paper).

Let `A ⊆ [0,1]` be a compact set of measure `> 3/4` avoiding every affine dyadic copy
(`DyadicAvoidanceStatement`), and let `Bₖ = {t : 8ᵏ t ∈ A ∩ [1/2, 1]}`, a copy of `A ∩ [1/2, 1]`
scaled into `[8⁻ᵏ/2, 8⁻ᵏ]`. The set `S = {0} ∪ ⋃ₖ Bₖ` is compact and has positive measure near `0`
at every scale. Two points of `S \ {0}` whose ratio lies strictly between `1/4` and `4` lie in the
same block. A dyadic copy `x + s·2⁻ⁿ` in `S` would therefore eventually stay in one block `Bₖ`
(if `x = 0`, consecutive points have ratio `2`; if `x ≠ 0`, the tail stays close to `x`), so its
tail, scaled by `8ᵏ`, would be a dyadic copy in `A`.
-/

open MeasureTheory Set

namespace DistanceSimilarity

/-- The `k`-th block `{t : 8ᵏ t ∈ A ∩ [1/2, 1]}`, contained in `[8⁻ᵏ/2, 8⁻ᵏ]`. -/
private def block (A : Set ℝ) (k : ℕ) : Set ℝ :=
  (fun t => (8 : ℝ) ^ k * t) ⁻¹' (A ∩ Icc (1 / 2) 1)

private lemma pos_of_mem_block {A : Set ℝ} {k : ℕ} {t : ℝ} (ht : t ∈ block A k) : 0 < t := by
  have h8 : (0 : ℝ) < 8 ^ k := by positivity
  by_contra h
  have := mul_nonpos_of_nonneg_of_nonpos h8.le (not_lt.1 h)
  linarith [ht.2.1]

private lemma le_one_of_mem_block {A : Set ℝ} {k : ℕ} {t : ℝ} (ht : t ∈ block A k) : t ≤ 1 :=
  (le_mul_of_one_le_left (pos_of_mem_block ht).le (one_le_pow₀ (by norm_num))).trans ht.2.2

/-- Points of an earlier block are at least four times larger than points of a later one. -/
private lemma four_mul_le_of_mem_block {A : Set ℝ} {j k : ℕ} (hjk : j < k) {y z : ℝ}
    (hy : y ∈ block A j) (hz : z ∈ block A k) : 4 * z ≤ y := by
  have h8j : (0 : ℝ) < 8 ^ j := by positivity
  have h8 : (8 : ℝ) ^ j * 8 ≤ 8 ^ k := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hjk
  have hz' : (8 : ℝ) ^ j * 8 * z ≤ 1 :=
    (mul_le_mul_of_nonneg_right h8 (pos_of_mem_block hz).le).trans hz.2.2
  have hy' := hy.2.1
  by_contra h
  have := mul_lt_mul_of_pos_left (not_le.1 h) h8j
  nlinarith

/-- Two points of `⋃ₖ Bₖ` whose ratio lies strictly between `1/4` and `4` lie in the same block. -/
private lemma block_eq {A : Set ℝ} {j k : ℕ} {y z : ℝ} (hy : y ∈ block A j) (hz : z ∈ block A k)
    (hyz : y < 4 * z) (hzy : z < 4 * y) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact absurd (four_mul_le_of_mem_block h hy hz) (not_le.2 hyz)
  · exact h
  · exact absurd (four_mul_le_of_mem_block h hz hy) (not_le.2 hzy)

/-- **Proposition 3.4 (positive measure at every scale is not enough).** Assume the dyadic case of
the Erdős similarity conjecture. There is a compact set `S ⊆ [0, 1]` containing `0` such that
`S ∩ [0, r]` has positive measure for every `r > 0`, but `S` contains no nontrivial affine copy of
`{2⁻ⁿ : n ≥ 1}`. -/
theorem exists_dyadicFree_pos_every_scale (hDy : DyadicAvoidanceStatement) :
    ∃ S : Set ℝ, IsCompact S ∧ S ⊆ Icc 0 1 ∧ (0 : ℝ) ∈ S ∧
      (∀ r : ℝ, 0 < r → 0 < volume (S ∩ Icc 0 r)) ∧ ¬ ContainsDyadicCopy S := by
  obtain ⟨A, hA01, hAc, hAvol, hAavoid⟩ := hDy (1 / 4) (by norm_num) (by norm_num)
  set S := insert (0 : ℝ) (⋃ k, block A k) with hS
  have hS01 : S ⊆ Icc 0 1 := by
    rintro t (rfl | ht)
    · exact ⟨le_rfl, zero_le_one⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.1 ht
      exact ⟨(pos_of_mem_block hk).le, le_one_of_mem_block hk⟩
  have hblock_closed : ∀ k, IsClosed (block A k) := fun k =>
    (hAc.isClosed.inter isClosed_Icc).preimage (continuous_const.mul continuous_id)
  -- `S` is closed: it is the intersection over `N` of `[0, 8⁻ᴺ] ∪ B₀ ∪ ⋯ ∪ B_{N-1}`.
  have hSclosed : IsClosed S := by
    have hSeq : S = ⋂ N : ℕ, (Icc 0 ((8 : ℝ)⁻¹ ^ N) ∪ ⋃ k ∈ Finset.range N, block A k) := by
      ext t
      simp only [mem_iInter, mem_union, mem_iUnion, Finset.mem_range, exists_prop]
      constructor
      · rintro (rfl | ht) N
        · exact Or.inl ⟨le_rfl, by positivity⟩
        · obtain ⟨k, hk⟩ := mem_iUnion.1 ht
          by_cases hkN : k < N
          · exact Or.inr ⟨k, hkN, hk⟩
          · refine Or.inl ⟨(pos_of_mem_block hk).le, ?_⟩
            have h8 : (0 : ℝ) < 8 ^ k := by positivity
            have htk : t ≤ (8 : ℝ)⁻¹ ^ k := by
              rw [inv_pow, ← one_div, le_div_iff₀ h8, mul_comm]; exact hk.2.2
            exact htk.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (not_lt.1 hkN))
      · intro h
        have ht0 : 0 ≤ t := by
          rcases h 0 with h0 | ⟨k, hk, -⟩
          · exact h0.1
          · simp at hk
        rcases ht0.eq_or_lt with rfl | htpos
        · exact mem_insert _ _
        · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one htpos (by norm_num : (8 : ℝ)⁻¹ < 1)
          rcases h N with hI | ⟨k, -, hk⟩
          · exact absurd hI.2 (not_le.2 hN)
          · exact mem_insert_of_mem _ (mem_iUnion.2 ⟨k, hk⟩)
    rw [hSeq]
    exact isClosed_iInter fun N =>
      isClosed_Icc.union (isClosed_biUnion_finset fun k _ => hblock_closed k)
  have hScpt : IsCompact S := isCompact_Icc.of_isClosed_subset hSclosed hS01
  -- the blocks have positive measure
  have hA'pos : 0 < volume (A ∩ Icc (1 / 2) 1) := by
    rw [pos_iff_ne_zero]
    intro h0
    have hsub : A ⊆ Ico 0 (1 / 2) ∪ A ∩ Icc (1 / 2) 1 := by
      intro t ht
      by_cases h : t < 1 / 2
      · exact Or.inl ⟨(hA01 ht).1, h⟩
      · exact Or.inr ⟨ht, not_lt.1 h, (hA01 ht).2⟩
    have hle := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
    rw [h0, add_zero, Real.volume_Ico] at hle
    have hlt : ENNReal.ofReal (1 / 2 - 0) < ENNReal.ofReal (1 - 1 / 4) := by
      rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num
    exact lt_irrefl _ ((hlt.trans hAvol).trans_le hle)
  have hblock_pos : ∀ k, 0 < volume (block A k) := fun k => by
    rw [block, Real.volume_preimage_mul_left (by positivity)]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' hA'pos.ne'
  refine ⟨S, hScpt, hS01, mem_insert _ _, fun r hr => ?_, ?_⟩
  · -- positive measure at every scale: `Bₖ ⊆ S ∩ [0, r]` once `8⁻ᵏ < r`
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (8 : ℝ)⁻¹ < 1)
    refine (hblock_pos k).trans_le (measure_mono fun t ht => ⟨mem_insert_of_mem _
      (mem_iUnion.2 ⟨k, ht⟩), (pos_of_mem_block ht).le, ?_⟩)
    have h8 : (0 : ℝ) < 8 ^ k := by positivity
    have htk : t ≤ (8 : ℝ)⁻¹ ^ k := by
      rw [inv_pow, ← one_div, le_div_iff₀ h8, mul_comm]; exact ht.2.2
    exact htk.trans hk.le
  · -- no dyadic copy
    rintro ⟨x, s, hs, hall⟩
    have hd : ∀ n : ℕ, 0 < dyadicPoint n := fun n => by unfold dyadicPoint; positivity
    have hblock_of : ∀ n, 1 ≤ n → x + s * dyadicPoint n ≠ 0 →
        ∃ k, x + s * dyadicPoint n ∈ block A k := fun n hn hne => by
      rcases hall n hn with h | h
      · exact absurd h hne
      · exact mem_iUnion.1 h
    -- some block contains a whole tail of the copy
    obtain ⟨k, N, hN1, htail⟩ : ∃ k N : ℕ, 1 ≤ N ∧
        ∀ n, N ≤ n → x + s * dyadicPoint n ∈ block A k := by
      rcases eq_or_ne x 0 with rfl | hx
      · -- `x = 0`: consecutive points have ratio `2`, so all lie in the block of the first one
        simp only [zero_add] at hblock_of ⊢
        obtain ⟨k, hk⟩ := hblock_of 1 le_rfl (mul_ne_zero hs (hd 1).ne')
        refine ⟨k, 1, le_rfl, fun n hn => ?_⟩
        induction n, hn using Nat.le_induction with
        | base => exact hk
        | succ n hn ih =>
          obtain ⟨j, hj⟩ := hblock_of (n + 1) (by omega) (mul_ne_zero hs (hd _).ne')
          have hpos := pos_of_mem_block hj
          have hrel : s * dyadicPoint n = 2 * (s * dyadicPoint (n + 1)) := by
            simp only [dyadicPoint, pow_succ]; ring
          have hjk := block_eq ih hj (by linarith) (by linarith)
          exact hjk ▸ hj
      · -- `x ≠ 0`: the tail stays within `|x|/8` of `x`, so all of it lies in one block
        obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one
          (div_pos (abs_pos.2 hx) (mul_pos (by norm_num : (0 : ℝ) < 8) (abs_pos.2 hs)))
          (by norm_num : (2 : ℝ)⁻¹ < 1)
        have hclose : ∀ n, N₀ + 1 ≤ n → |s * dyadicPoint n| < |x| / 8 := fun n hn => by
          rw [abs_mul, abs_of_pos (hd n)]
          have hle : dyadicPoint n ≤ (2 : ℝ)⁻¹ ^ N₀ :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          have h8s : (0 : ℝ) < 8 * |s| := by positivity
          rw [lt_div_iff₀ h8s] at hN₀
          nlinarith [abs_pos.2 hs]
        have hnear : ∀ n, N₀ + 1 ≤ n →
            x - |x| / 8 < x + s * dyadicPoint n ∧ x + s * dyadicPoint n < x + |x| / 8 :=
          fun n hn => by
            have := abs_lt.1 (hclose n hn); constructor <;> linarith [this.1, this.2]
        rcases lt_or_gt_of_ne hx with hneg | hposx
        · -- `x < 0`: the tail is negative, but `S ⊆ [0, 1]`
          exfalso
          have h1 := (hnear (N₀ + 1) le_rfl).2
          have h2 := (hS01 (hall (N₀ + 1) (by omega))).1
          rw [abs_of_neg hneg] at h1
          linarith
        · rw [abs_of_pos hposx] at hnear
          have hne : ∀ n, N₀ + 1 ≤ n → x + s * dyadicPoint n ≠ 0 := fun n hn =>
            (by linarith [(hnear n hn).1] : 0 < x + s * dyadicPoint n).ne'
          obtain ⟨k, hk⟩ := hblock_of (N₀ + 1) (by omega) (hne _ le_rfl)
          refine ⟨k, N₀ + 1, by omega, fun n hn => ?_⟩
          obtain ⟨j, hj⟩ := hblock_of n (by omega) (hne n hn)
          have h1 := hnear n hn
          have h2 := hnear (N₀ + 1) le_rfl
          have hjk := block_eq hj hk (by linarith) (by linarith)
          exact hjk ▸ hj
    -- scaling the tail by `8ᵏ` gives a dyadic copy in `A`
    obtain ⟨m, hm1, hmA⟩ := hAavoid ((8 : ℝ) ^ k * x) ((8 : ℝ) ^ k * s * dyadicPoint N)
      (mul_ne_zero (mul_ne_zero (by positivity) hs) (hd N).ne')
    apply hmA
    have := (htail (N + m) (by omega)).1
    convert this using 1
    simp only [dyadicPoint, pow_add]
    ring

end DistanceSimilarity
