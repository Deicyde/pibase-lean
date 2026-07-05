module

public import Mathlib.Topology.Order

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S11

/- Space 11: Excluded Point Topology on a Three-Point Set.
See https://topology.pi-base.org/spaces/S000011.
Carrier `Fin 3`, with particular point `p = 0`; a set is open iff it does not
contain `p`, or it is the whole space. -/

/-- Excluded Point Topology on a Three-Point Set (pi-Base S11). -/
def S11 : Type := Fin 3

/-- The open sets: every subset avoiding the excluded point `0`, together with
the whole space. -/
instance : TopologicalSpace S11 :=
  TopologicalSpace.generateFrom
    ({s : Set (Fin 3) | (0 : Fin 3) ∉ s} ∪ {(Set.univ : Set (Fin 3))})

end S11
end PiBase.Spaces
