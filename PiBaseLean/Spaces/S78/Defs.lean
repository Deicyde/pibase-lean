module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces

/- Space 78: Tychonoff plank.
See https://topology.pi-base.org/spaces/S000078.
The product `[0, ω₁] × [0, ω]`, i.e. the product of the ordinal space ω₁+1 (S36) and
the ordinal space ω+1 (S20), each carrying the order topology; here realized as the
product of `{o : Ordinal // o ≤ ω₁}` (order topology) and `OnePoint ℕ`
(the ordinal space ω+1, as the one-point compactification of the discrete space ℕ),
with the product topology. -/

/-- The factor `[0, ω₁]` of the Tychonoff plank: ordinals at most the least
uncountable ordinal ω₁, with the order topology (pi-Base S36). -/
def S78.Fst : Type 1 := {o : Ordinal.{0} // o ≤ ω₁}

noncomputable instance : LinearOrder S78.Fst :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o ≤ ω₁})

noncomputable instance : TopologicalSpace S78.Fst := Preorder.topology S78.Fst

instance : OrderTopology S78.Fst := ⟨rfl⟩

/-- The factor `[0, ω]` of the Tychonoff plank: the ordinal space ω+1, realized as
the one-point compactification of the discrete space ℕ (pi-Base S20). -/
def S78.Snd : Type := OnePoint ℕ

instance : TopologicalSpace S78.Snd := inferInstanceAs (TopologicalSpace (OnePoint ℕ))

/-- Tychonoff plank (pi-Base S78): the product `[0, ω₁] × [0, ω]`. -/
def S78 : Type 1 := S78.Fst × S78.Snd

noncomputable instance : TopologicalSpace S78 :=
  inferInstanceAs (TopologicalSpace (S78.Fst × S78.Snd))

end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S78 as a bundled `Space` (carrier + topology). -/
noncomputable def S78 : Space := ⟨PiBase.Spaces.S78, inferInstance⟩

end PiBase.Formal
