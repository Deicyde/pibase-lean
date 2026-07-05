module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Constructions

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S218

/- Space 218: Product $\omega_1\times(\omega_1+1)$.
See https://topology.pi-base.org/spaces/S000218.
The product of the ordinal space ω₁ (S35) and the ordinal space ω₁+1 (S36),
each carrying the order topology, with the product topology. -/

/-- The ordinals below the least uncountable ordinal ω₁ (the carrier of S35),
carrying the order topology. -/
def S218.Left : Type 1 := {o : Ordinal.{0} // o < ω₁}

/-- The ordinals at most the least uncountable ordinal ω₁ (the carrier of S36),
carrying the order topology. -/
def S218.Right : Type 1 := {o : Ordinal.{0} // o ≤ ω₁}

noncomputable instance : LinearOrder S218.Left :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o < ω₁})

noncomputable instance : LinearOrder S218.Right :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o ≤ ω₁})

noncomputable instance : TopologicalSpace S218.Left := Preorder.topology S218.Left

noncomputable instance : TopologicalSpace S218.Right := Preorder.topology S218.Right

instance : OrderTopology S218.Left := ⟨rfl⟩

instance : OrderTopology S218.Right := ⟨rfl⟩

/-- Product $\omega_1\times(\omega_1+1)$ (pi-Base S218): the product of the ordinal
space ω₁ and the ordinal space ω₁+1. -/
def S218 : Type 1 := S218.Left × S218.Right

noncomputable instance : TopologicalSpace S218 :=
  inferInstanceAs (TopologicalSpace (S218.Left × S218.Right))

end S218
end PiBase.Spaces
