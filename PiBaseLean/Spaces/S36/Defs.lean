module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.Order.Basic

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S36

/- Space 36: Ordinal space ω₁+1.
See https://topology.pi-base.org/spaces/S000036.
The set of ordinals at most the least uncountable ordinal ω₁, with the order topology. -/

/-- Ordinal space ω₁+1 (pi-Base S36): the ordinals up to and including the least
uncountable ordinal ω₁, carrying the order topology. -/
def S36 : Type 1 := {o : Ordinal.{0} // o ≤ ω₁}

noncomputable instance : LinearOrder S36 :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o ≤ ω₁})

noncomputable instance : TopologicalSpace S36 := Preorder.topology S36

instance : OrderTopology S36 := ⟨rfl⟩

end S36
end PiBase.Spaces
