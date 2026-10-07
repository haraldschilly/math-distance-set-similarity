import DistanceSimilarity.Statements

/-!
# Patterns on the real line

Elementary facts about affine copies of geometric sequences `{qⁿ : n ≥ 1}` (`0 < q < 1`) and of
bounded sets:

* an interval, or more generally any set with nonempty interior, contains affine copies of every
  bounded set and of every geometric sequence;
* adding the limit point `0` to a set avoiding all affine copies of `{qⁿ}` keeps it avoiding them
  (Lemma 4.1 of the paper).
-/

open Set Metric

namespace DistanceSimilarity

variable {q : ℝ}

theorem ContainsGeomCopy.mono {P Q : Set ℝ} (h : ContainsGeomCopy q P) (hPQ : P ⊆ Q) :
    ContainsGeomCopy q Q := by
  obtain ⟨x, s, hs, hx⟩ := h
  exact ⟨x, s, hs, fun n hn => hPQ (hx n hn)⟩

theorem ContainsDyadicCopy.mono {P Q : Set ℝ} (h : ContainsDyadicCopy P) (hPQ : P ⊆ Q) :
    ContainsDyadicCopy Q :=
  ContainsGeomCopy.mono (q := 2⁻¹) h hPQ

theorem ContainsAffineCopy.mono {F P Q : Set ℝ} (h : ContainsAffineCopy F P) (hPQ : P ⊆ Q) :
    ContainsAffineCopy F Q := by
  obtain ⟨x, s, hs, hx⟩ := h
  exact ⟨x, s, hs, fun a ha => hPQ (hx a ha)⟩

/-- A nondegenerate closed interval contains an affine copy of every set `F ⊆ [0, M]`. -/
theorem containsAffineCopy_Icc {a b M : ℝ} (hab : a < b) (hM : 0 < M) {F : Set ℝ}
    (hF : F ⊆ Icc 0 M) : ContainsAffineCopy F (Icc a b) := by
  refine ⟨a, (b - a) / M, (div_pos (sub_pos.2 hab) hM).ne', fun t ht => ⟨?_, ?_⟩⟩
  · have := (hF ht).1
    have : 0 ≤ (b - a) / M * t := mul_nonneg (div_pos (sub_pos.2 hab) hM).le this
    linarith
  · have ht1 := (hF ht).2
    have : (b - a) / M * t ≤ (b - a) / M * M :=
      mul_le_mul_of_nonneg_left ht1 (div_pos (sub_pos.2 hab) hM).le
    rw [div_mul_cancel₀ _ hM.ne'] at this
    linarith

/-- A nondegenerate closed interval contains an affine copy of `{qⁿ : n ≥ 1}` for `0 < q < 1`. -/
theorem containsGeomCopy_Icc (hq0 : 0 < q) (hq1 : q < 1) {a b : ℝ} (hab : a < b) :
    ContainsGeomCopy q (Icc a b) := by
  obtain ⟨x, s, hs, h⟩ := containsAffineCopy_Icc (F := range fun n : ℕ => q ^ n) hab one_pos
    (by rintro _ ⟨n, rfl⟩; exact ⟨by positivity, pow_le_one₀ hq0.le hq1.le⟩)
  exact ⟨x, s, hs, fun n _ => h _ ⟨n, rfl⟩⟩

/-- A set with nonempty interior contains a nondegenerate closed interval. -/
theorem exists_Icc_subset_of_interior_nonempty {P : Set ℝ} (hP : (interior P).Nonempty) :
    ∃ a b : ℝ, a < b ∧ Icc a b ⊆ P := by
  obtain ⟨x, hx⟩ := hP
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  refine ⟨x - ε / 2, x + ε / 2, by linarith, fun y hy => interior_subset (hball ?_)⟩
  rw [mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

/-- **Proposition C(i).** A set of reals with nonempty interior contains an affine copy of every
bounded set `F ⊆ [0, M]`. -/
theorem containsAffineCopy_of_interior_nonempty {P : Set ℝ} (hP : (interior P).Nonempty)
    {M : ℝ} (hM : 0 < M) {F : Set ℝ} (hF : F ⊆ Icc 0 M) : ContainsAffineCopy F P := by
  obtain ⟨a, b, hab, hsub⟩ := exists_Icc_subset_of_interior_nonempty hP
  exact (containsAffineCopy_Icc hab hM hF).mono hsub

/-- **Proposition C(i), geometric sequences.** A set of reals with nonempty interior contains an
affine copy of `{qⁿ : n ≥ 1}` for every `0 < q < 1`. -/
theorem containsGeomCopy_of_interior_nonempty (hq0 : 0 < q) (hq1 : q < 1) {P : Set ℝ}
    (hP : (interior P).Nonempty) : ContainsGeomCopy q P := by
  obtain ⟨a, b, hab, hsub⟩ := exists_Icc_subset_of_interior_nonempty hP
  exact (containsGeomCopy_Icc hq0 hq1 hab).mono hsub

/-- **Lemma 4.1 (adding the limit point).** If `A` contains no nontrivial affine copy of
`{qⁿ : n ≥ 1}` (`0 < q < 1`), neither does `A ∪ {0}`: a copy meets `0` at most once, and its tail
after that point is again an affine copy of `{qⁿ}`. -/
theorem not_containsGeomCopy_insert_zero (hq0 : 0 < q) (hq1 : q < 1) {A : Set ℝ}
    (hA : ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x + s * q ^ n ∉ A) :
    ¬ ContainsGeomCopy q (insert 0 A) := by
  rintro ⟨x, s, hs, hall⟩
  by_cases h0 : ∃ m : ℕ, x + s * q ^ m = 0
  · obtain ⟨m, hm⟩ := h0
    obtain ⟨n, hn, hnA⟩ := hA x (s * q ^ m) (mul_ne_zero hs (pow_pos hq0 m).ne')
    rcases hall (m + n) (by omega) with hzero | hmem
    · have : q ^ (m + n) = q ^ m := mul_left_cancel₀ hs (by linarith)
      have := pow_right_injective₀ hq0 hq1.ne this
      omega
    · exact hnA (by rwa [pow_add, ← mul_assoc] at hmem)
  · push Not at h0
    obtain ⟨n, hn, hnA⟩ := hA x s hs
    rcases hall n hn with hzero | hmem
    · exact h0 n hzero
    · exact hnA hmem

end DistanceSimilarity
