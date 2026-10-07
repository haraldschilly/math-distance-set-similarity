import DistanceSimilarity.Statements
import OAI.MeasureTheory.Falconer.Campaign123PlanarFurstenbergProof

/-! Kernel check: OAI's proof of the Falconer distance conjecture has exactly the type of our hypothesis. -/

theorem DistanceSimilarity.falconer_holds : DistanceSimilarity.FalconerStatement :=
  OAI.Falconer.falconer_distance_conjecture

#print axioms DistanceSimilarity.falconer_holds
