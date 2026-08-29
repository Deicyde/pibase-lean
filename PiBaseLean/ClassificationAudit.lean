import PiBaseLean.Goal

/-!
# Machine-readable classification audit

This executable reports the stable catalogue and the status counts obtained by evaluating the
canonical `piBaseClassificationPlan`. Its single line of standard output is deterministic JSON.
-/

open PiBase.Formal

namespace PiBase.ClassificationAudit

private abbrev AuditPair : Type := PiBaseImplicationPair.{0}

private structure StatusCounts where
  proved : Nat
  refuted : Nat
  variesUnder : Nat
  openPairs : Nat

private inductive StatusBucket
  | proved
  | refuted
  | variesUnder
  | open
  deriving DecidableEq

private def statusBucket : Option ImplicationStatus → StatusBucket
  | some .proved => .proved
  | some .refuted => .refuted
  | some (.variesUnder _ _) => .variesUnder
  | none => .open

private def countStatus (bucket : StatusBucket) : Nat :=
  ((Finset.univ : Finset AuditPair).filter fun pair ↦
    statusBucket (piBaseClassificationPlan pair) = bucket).card

private def statusCounts : StatusCounts :=
  ⟨countStatus .proved, countStatus .refuted, countStatus .variesUnder, countStatus .open⟩

private def renderNatList (values : List Nat) : String :=
  "[" ++ String.intercalate "," (values.map toString) ++ "]"

private def renderBool (value : Bool) : String :=
  if value then "true" else "false"

/-- The deterministic JSON document emitted by `classificationAudit`. -/
def json (_sound : piBaseClassificationPlan.{0}.Sound) : String :=
  let ids := piBasePropertyIds.{0}
  let counts := statusCounts
  "{\"schemaVersion\":1," ++
    "\"scope\":\"positive-ordered-distinct\"," ++
    "\"planDeclaration\":\"PiBase.Formal.piBaseClassificationPlan\"," ++
    "\"goalDeclaration\":\"PiBase.Formal.PiBaseProjectGoal\"," ++
    "\"propertyIds\":" ++ renderNatList ids ++ "," ++
    "\"propertyCount\":" ++ toString ids.length ++ "," ++
    "\"pairCount\":" ++ toString (Fintype.card AuditPair) ++ "," ++
    "\"statuses\":{" ++
      "\"proved\":" ++ toString counts.proved ++ "," ++
      "\"refuted\":" ++ toString counts.refuted ++ "," ++
      "\"variesUnder\":" ++ toString counts.variesUnder ++ "," ++
      "\"open\":" ++ toString counts.openPairs ++ "}," ++
    "\"sound\":true," ++
    "\"complete\":" ++ renderBool (counts.openPairs == 0) ++ "}"

end PiBase.ClassificationAudit

def main : IO Unit :=
  IO.println (PiBase.ClassificationAudit.json piBaseClassificationPlan_sound)
