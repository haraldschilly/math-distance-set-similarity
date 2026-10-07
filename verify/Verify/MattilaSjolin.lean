import DistanceSimilarity.Statements
import MattilaSjolin.Main

/-! Kernel check: the Mattila–Sjölin formalization (github.com/haraldschilly/math-mattila-sjolin,
`MattilaSjolin.mattilaSjolin`) proves exactly the hypothesis `MattilaSjolinStatement`. -/

theorem DistanceSimilarity.mattilaSjolin_holds : DistanceSimilarity.MattilaSjolinStatement :=
  MattilaSjolin.mattilaSjolin

#print axioms DistanceSimilarity.mattilaSjolin_holds
