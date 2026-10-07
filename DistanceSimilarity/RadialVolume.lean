import Mathlib

/-!
# Volume of radial sets

For a compact `A ⊆ [0,1]` with `λ(A) = c`, the radial set `{y ∈ ℝ^d : ‖y‖ ∈ A}` has volume at least
`c^d · vol(B(0,1))`. The proof uses polar coordinates and the monotone rearrangement inequality
`∫_A r^{d-1} dr ≥ ∫_0^c r^{d-1} dr`.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace DistanceSimilarity

/-- Rearrangement: for `A ⊆ [0,1]` of measure `c` and `n : ℕ`, `∫_A r^n ≥ ∫_0^c r^n = c^(n+1)/(n+1)`. -/
theorem setIntegral_pow_ge {A : Set ℝ} (hAm : MeasurableSet A) (hA01 : A ⊆ Icc 0 1) (n : ℕ) :
    (volume.real A) ^ (n + 1) / (n + 1) ≤ ∫ y in A, y ^ n := by
  set c := volume.real A with hc
  have hAfin : volume A ≠ ∞ :=
    ((measure_mono hA01).trans_lt measure_Icc_lt_top).ne
  set B := Icc (0 : ℝ) c with hB
  have hBm : MeasurableSet B := measurableSet_Icc
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hint : ∀ s : Set ℝ, s ⊆ Icc 0 1 → IntegrableOn (fun y : ℝ => y ^ n) s := fun s hs =>
    ((continuous_pow n).continuousOn.integrableOn_compact isCompact_Icc).mono_set hs
  have hc1 : c ≤ 1 := by
    have := measureReal_mono hA01 (by simp : volume (Icc (0 : ℝ) 1) ≠ ∞)
    simpa [hc] using this
  have hB01 : B ⊆ Icc 0 1 := Icc_subset_Icc le_rfl hc1
  -- ∫_B r^n = c^(n+1)/(n+1)
  have hBint : ∫ y in B, y ^ n = c ^ (n + 1) / (n + 1) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc0, integral_pow]
    simp
  -- split both integrals along A ∩ B
  have hsplitA : ∫ y in A, y ^ n = (∫ y in A ∩ B, y ^ n) + ∫ y in A \ B, y ^ n := by
    have hd : Disjoint (A ∩ B) (A \ B) := Disjoint.mono_left inter_subset_right disjoint_sdiff_right
    have h := setIntegral_union hd (hAm.diff hBm) (hint _ (inter_subset_left.trans hA01))
      (hint _ (sdiff_subset.trans hA01))
    rw [inter_union_sdiff] at h
    exact h
  have hsplitB : ∫ y in B, y ^ n = (∫ y in A ∩ B, y ^ n) + ∫ y in B \ A, y ^ n := by
    have hd : Disjoint (A ∩ B) (B \ A) := Disjoint.mono_left inter_subset_left disjoint_sdiff_right
    have hu : A ∩ B ∪ B \ A = B := by rw [inter_comm]; exact inter_union_sdiff B A
    have h := setIntegral_union hd (hBm.diff hAm) (hint _ (inter_subset_left.trans hA01))
      (hint _ (sdiff_subset.trans hB01))
    rw [hu] at h
    exact h
  -- on `A \ B` the integrand is ≥ c^n, on `B \ A` it is ≤ c^n
  have hlow : c ^ n * volume.real (A \ B) ≤ ∫ y in A \ B, y ^ n := by
    have hfin : volume (A \ B) ≠ ∞ := ne_top_of_le_ne_top hAfin (measure_mono sdiff_subset)
    rw [mul_comm, ← smul_eq_mul, ← setIntegral_const]
    refine setIntegral_mono_on (integrableOn_const hfin) (hint _ (sdiff_subset.trans hA01))
      (hAm.diff hBm) fun y hy => ?_
    have hyc : c ≤ y := by
      by_contra h
      exact hy.2 ⟨(hA01 hy.1).1, (not_le.1 h).le⟩
    exact pow_le_pow_left₀ hc0 hyc n
  have hup : ∫ y in B \ A, y ^ n ≤ c ^ n * volume.real (B \ A) := by
    have hfin : volume (B \ A) ≠ ∞ :=
      ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono sdiff_subset)
    rw [mul_comm, ← smul_eq_mul, ← setIntegral_const]
    refine setIntegral_mono_on (hint _ (sdiff_subset.trans hB01)) (integrableOn_const hfin)
      (hBm.diff hAm) fun y hy => ?_
    exact pow_le_pow_left₀ hy.1.1 hy.1.2 n
  -- the two defect sets have the same measure
  have hmeas : volume.real (A \ B) = volume.real (B \ A) := by
    have h1 := measureReal_sdiff_add_inter (μ := volume) (s := A) (t := B) hBm (by simpa using hAfin)
    have h2 := measureReal_sdiff_add_inter (μ := volume) (s := B) (t := A) hAm
      measure_Icc_lt_top.ne
    have hBc : volume.real B = c := by
      simp [hB, Real.volume_real_Icc, hc0]
    rw [inter_comm] at h2
    linarith
  have := mul_le_mul_of_nonneg_left hmeas.ge (pow_nonneg hc0 n)
  linarith

/-- Polar coordinates for radial sets over `A ⊆ [0,1]`:
`vol {y : ‖y‖ ∈ A} = d · vol(B(0,1)) · ∫_A r^(d-1) dr`. -/
theorem volume_real_norm_preimage {d : ℕ} (hd : 1 ≤ d) {A : Set ℝ} (hAc : IsCompact A)
    (hA01 : A ⊆ Icc 0 1) :
    volume.real ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) ⁻¹' A) =
      d * (volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) * ∫ y in A, y ^ (d - 1)) := by
  have hAm : MeasurableSet A := hAc.measurableSet
  have hm : MeasurableSet ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) ⁻¹' A) :=
    measurable_norm hAm
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hpolar := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d)))
    (A.indicator (fun _ => (1 : ℝ)))
  have hlhs : ∫ x : EuclideanSpace ℝ (Fin d), A.indicator (fun _ => (1 : ℝ)) ‖x‖ =
      volume.real ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) ⁻¹' A) := by
    rw [← integral_indicator_one hm]
    congr 1
  have hint : IntegrableOn (fun y : ℝ => y ^ (d - 1)) A :=
    (continuous_pow (d - 1)).continuousOn.integrableOn_compact hAc
  have hrad : ∫ y in Ioi (0 : ℝ),
      y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1) • A.indicator (fun _ => (1 : ℝ)) y =
      ∫ y in A, y ^ (d - 1) := by
    have h1 : (fun y : ℝ =>
        y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1) • A.indicator (fun _ => (1 : ℝ)) y) =
        A.indicator (fun y => y ^ (d - 1)) := by
      ext y; by_cases hy : y ∈ A <;> simp [hy]
    have hnull : volume (A \ Ioi (0 : ℝ)) = 0 :=
      measure_mono_null (fun y hy => by
        have h0 := (hA01 hy.1).1
        have h1 : ¬ (0 : ℝ) < y := hy.2
        exact le_antisymm (not_lt.1 h1) h0) (measure_singleton 0)
    rw [h1, setIntegral_indicator hAm, ← integral_inter_add_sdiff measurableSet_Ioi hint,
      setIntegral_measure_zero _ hnull, add_zero, inter_comm]
  rw [← hlhs, hpolar, hrad, finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul]

/-- **Lemma 4.2 (volume of radial sets).** If `A ⊆ [0,1]` is compact, then
`vol {y ∈ ℝ^d : ‖y‖ ∈ A} ≥ λ(A)^d · vol(B(0,1))`. -/
theorem volume_norm_preimage_ge {d : ℕ} (hd : 1 ≤ d) {A : Set ℝ} (hAc : IsCompact A)
    (hA01 : A ⊆ Icc 0 1) :
    ENNReal.ofReal ((volume.real A) ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      volume ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) ⁻¹' A) := by
  have hball : volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hKfin : volume ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) ⁻¹' A) ≠ ∞ := by
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := 0) (r := 1)).ne
      (measure_mono fun y hy => ?_)
    simpa using (hA01 hy).2
  have hrear := setIntegral_pow_ge hAc.measurableSet hA01 (d - 1)
  have hd' : (d - 1 + 1 : ℕ) = d := by omega
  rw [hd'] at hrear
  have hcast : ((d - 1 : ℕ) : ℝ) + 1 = d := by
    rw [Nat.cast_sub hd]; ring
  rw [hcast] at hrear
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hreal : (volume.real A) ^ d * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      volume.real ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) ⁻¹' A) := by
    rw [volume_real_norm_preimage hd hAc hA01]
    have hb : 0 ≤ volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := measureReal_nonneg
    have := mul_le_mul_of_nonneg_left hrear hb
    rw [div_eq_mul_inv] at this
    calc (volume.real A) ^ d * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
        = d * (volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) *
            ((volume.real A) ^ d * (d : ℝ)⁻¹)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this hdpos.le
  rw [← ENNReal.ofReal_toReal hball, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_toReal hKfin]
  exact ENNReal.ofReal_le_ofReal hreal

end DistanceSimilarity
