module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S7

/- Space 7: Particular point topology on a three-point set.
See https://topology.pi-base.org/spaces/S000007.
On X = {0, 1, 2}, a set is open iff it contains the particular point 0 or is empty. -/

/-- Particular point topology on a three-point set (pi-Base S7). -/
def S7 : Type := Fin 3

instance : TopologicalSpace S7 :=
  TopologicalSpace.generateFrom {s : Set S7 | (0 : Fin 3) ∈ s}

instance : Finite S7 := inferInstanceAs (Finite (Fin 3))
instance : DecidableEq S7 := inferInstanceAs (DecidableEq (Fin 3))

end S7
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S7 as a bundled `Space` (carrier + topology). -/
noncomputable def S7 : Space := ⟨PiBase.Spaces.S7.S7, inferInstance⟩

end PiBase.Formal
