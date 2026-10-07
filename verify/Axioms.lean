import DistanceSimilarity

/-! Every result of the paper, with the axioms it depends on. The external inputs enter only as
explicit hypotheses (`FalconerStatement`, `DyadicAvoidanceStatement`,
`GeometricAvoidanceStatement q`, `MattilaSjolinStatement`), never as axioms. -/

-- Section 1.2
#print axioms DistanceSimilarity.volume_distSet_inter_Icc_pos
-- Theorem A, Lemma 3.1, Remark 3.2
#print axioms DistanceSimilarity.finite_pattern_distSet
#print axioms DistanceSimilarity.exists_finite_pattern_distSet
#print axioms DistanceSimilarity.eventually_volume_pattern_pos
#print axioms DistanceSimilarity.volume_pattern_pairs_pos
-- Lemmas 4.1–4.4, Theorem B, Remark 4.5
#print axioms DistanceSimilarity.not_containsGeomCopy_insert_zero
#print axioms DistanceSimilarity.volume_norm_preimage_ge
#print axioms DistanceSimilarity.dimH_eq_of_volume_pos
#print axioms DistanceSimilarity.exists_Ico_subset_distSet
#print axioms DistanceSimilarity.Icc_subset_pinnedDistSet
#print axioms DistanceSimilarity.pinned_dyadic_obstruction
#print axioms DistanceSimilarity.pinned_geometric_obstruction
-- Proposition C, Remark C'
#print axioms DistanceSimilarity.distSet_containsAffineCopy_of_interior
#print axioms DistanceSimilarity.distSet_containsAffineCopy_of_volume_pos
#print axioms DistanceSimilarity.counterexample_properties
#print axioms DistanceSimilarity.window_of_mattilaSjolin
-- Section 6
#print axioms DistanceSimilarity.not_containsGeomCopy_pinnedDistSet_iff
