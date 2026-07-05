module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.UnitInterval

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S104

/- Space 104: Product of the first-uncountable ordinal with the continuum-power of
unit intervals.
See https://topology.pi-base.org/spaces/S000104.
The product topology on ω₁ (S35, order topology) crossed with I^I (S103, product
topology on functions I → I). -/

/-- The ordinals below the least uncountable ordinal ω₁ (used to build S104),
carrying the order topology. -/
def S104.Omega1 : Type 1 := {o : Ordinal.{0} // o < ω₁}

noncomputable instance : LinearOrder S104.Omega1 :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o < ω₁})

noncomputable instance : TopologicalSpace S104.Omega1 := Preorder.topology S104.Omega1

instance : OrderTopology S104.Omega1 := ⟨rfl⟩

/-- The continuum power of `[0,1]`: functions `I → I` with the topology of pointwise
convergence (used to build S104). -/
def S104.IPowI : Type := (unitInterval → unitInterval)

noncomputable instance : TopologicalSpace S104.IPowI :=
  inferInstanceAs (TopologicalSpace (unitInterval → unitInterval))

/-- Product of the first-uncountable ordinal with the continuum-power of unit intervals
(pi-Base S104): `ω₁ × I^I`, with the product topology. -/
def S104 : Type 1 := S104.Omega1 × S104.IPowI

noncomputable instance : TopologicalSpace S104 :=
  inferInstanceAs (TopologicalSpace (S104.Omega1 × S104.IPowI))

end S104
end PiBase.Spaces
