import DistanceSimilarity

/-! Every result of the paper, with the axioms it depends on. The external inputs enter only as
explicit hypotheses (`FalconerStatement`, `DyadicAvoidanceStatement`,
`GeometricAvoidanceStatement q`, `MattilaSjolinStatement`), never as axioms. -/

-- Lemma 3.1, Theorem A, Proposition 3.2, Lemma 3.3, Proposition 3.4
#print axioms DistanceSimilarity.eventually_volume_pattern_pos
#print axioms DistanceSimilarity.finite_pattern_distSet
#print axioms DistanceSimilarity.exists_finite_pattern_distSet
#print axioms DistanceSimilarity.volume_pattern_pairs_pos
#print axioms DistanceSimilarity.volume_distSet_inter_Icc_pos
#print axioms DistanceSimilarity.exists_dyadicFree_pos_every_scale
-- Lemmas 4.1–4.5, Theorem 4.6, Theorem B
#print axioms DistanceSimilarity.not_containsGeomCopy_insert_zero
#print axioms DistanceSimilarity.volume_norm_preimage_ge
#print axioms DistanceSimilarity.dimH_eq_of_volume_pos
#print axioms DistanceSimilarity.exists_Ico_subset_distSet
#print axioms DistanceSimilarity.Icc_subset_pinnedDistSet
#print axioms DistanceSimilarity.pinned_geometric_obstruction
#print axioms DistanceSimilarity.pinned_dyadic_obstruction
-- Proposition C, Remark 5.1
#print axioms DistanceSimilarity.distSet_containsAffineCopy_of_interior
#print axioms DistanceSimilarity.distSet_containsAffineCopy_of_volume_pos
#print axioms DistanceSimilarity.counterexample_properties
#print axioms DistanceSimilarity.window_of_mattilaSjolin
-- Lemma 6.1
#print axioms DistanceSimilarity.not_containsGeomCopy_pinnedDistSet_iff
