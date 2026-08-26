module

public import Lean

@[expose] public meta section

namespace PiBase.Audit.Meta

open Lean

/-- Collect the transitive axioms used by a declaration after checking that it exists. -/
def collectAxioms (declName : Name) : CoreM (Array Name) := do
  discard <| getConstInfo declName
  Lean.collectAxioms declName

/-- Test definitional equality, allowing unification of fresh elaboration metavariables. -/
def isDefEq (lhs rhs : Expr) : MetaM Bool :=
  Lean.Meta.isDefEq lhs rhs

/-- Require definitional equality and report both elaborated expressions on failure. -/
def assertDefEq (description : String) (actual expected : Expr) : MetaM Unit := do
  unless ← isDefEq actual expected do
    let actual ← Lean.Meta.whnf actual
    let expected ← Lean.Meta.whnf expected
    throwError "{description}\nactual:   {actual}\nexpected: {expected}"

end PiBase.Audit.Meta
