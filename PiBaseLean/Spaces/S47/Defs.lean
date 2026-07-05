module

public import Mathlib.Topology.Order
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S47

/- Space 47: Countable sum of Sierpinski spaces (a.k.a. Hjalmar Ekdal topology).
See https://topology.pi-base.org/spaces/S000047.
Carrier `X = ℕ` (the positive integers); `U ⊆ X` is declared open iff for every
odd `p ∈ U`, `p + 1 ∈ U` also. This collection of sets is already closed under
arbitrary unions and finite intersections, so `generateFrom` of it reproduces it
exactly. It is the topological sum of countably many copies of the Sierpinski
space (pi-Base S10), pairing up each odd `p` with its successor `p + 1`. -/

/-- Countable sum of Sierpinski spaces (pi-Base S47), on the carrier `ℕ`. -/
def S47 : Type := ℕ

/-- `U` is open iff every odd `p ∈ U` also has `p + 1 ∈ U`. -/
instance : TopologicalSpace S47 :=
  TopologicalSpace.generateFrom {U : Set ℕ | ∀ p ∈ U, Odd p → p + 1 ∈ U}

end S47
end PiBase.Spaces
