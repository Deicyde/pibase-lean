module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.Order.Basic
public import Mathlib.Data.Sum.Order

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S141

/- Space 141: Ordered space ω₁+1+ω*.
See https://topology.pi-base.org/spaces/S000141.
The linear sum, in order, of: ω₁ (the ordinals below the least uncountable ordinal,
as in S35), a single extra point, and ω* (the natural numbers with the reversed
order) -- carrying the order topology of this concatenated linear order. -/

/-- The ordinals below the least uncountable ordinal ω₁ (as in pi-Base S35), the
underlying carrier of the ω₁ summand here. -/
def Omega1 : Type 1 := {o : Ordinal.{0} // o < ω₁}

noncomputable instance : LinearOrder Omega1 :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o < ω₁})

/-- Ordered space ω₁+1+ω* (pi-Base S141): the ordinals below ω₁, followed by one
more point, followed by ℕ in reverse order, carrying the order topology. -/
def S141 : Type 1 := (Omega1 ⊕ₗ PUnit.{1}) ⊕ₗ ℕᵒᵈ

noncomputable instance : LinearOrder S141 :=
  inferInstanceAs (LinearOrder ((Omega1 ⊕ₗ PUnit.{1}) ⊕ₗ ℕᵒᵈ))

noncomputable instance : TopologicalSpace S141 := Preorder.topology S141

instance : OrderTopology S141 := ⟨rfl⟩

end S141
end PiBase.Spaces
