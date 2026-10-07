import DistanceSimilarity.Statements
import OAI.MeasureTheory.DyadicAvoidance.Main

/-! Kernel check: OAI's proof of the dyadic case has exactly the type of our hypothesis. -/

theorem DistanceSimilarity.dyadicAvoidance_holds : DistanceSimilarity.DyadicAvoidanceStatement :=
  OAI.Problem310.dyadic_affine_avoidance

#print axioms DistanceSimilarity.dyadicAvoidance_holds
