module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S188

/- Space 188: Sum of singleton and Sierpinski space.
See https://topology.pi-base.org/spaces/S000188.
X = {0, 1, 2} with open sets {∅, {0}, {1}, {0, 1}, {1, 2}, X}, i.e. the topological sum of
the singleton {0} (S162) and the Sierpinski space {1, 2} (S10). -/

/-- Sum of singleton and Sierpinski space (pi-Base S188). -/
def S188 : Type := Fin 3

instance : TopologicalSpace S188 :=
  TopologicalSpace.generateFrom
    {({0} : Set (Fin 3)), ({1} : Set (Fin 3)), ({1, 2} : Set (Fin 3))}

instance : Finite S188 := inferInstanceAs (Finite (Fin 3))

instance : DecidableEq S188 := inferInstanceAs (DecidableEq (Fin 3))

end S188
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S188 as a bundled `Space` (carrier + topology). -/
noncomputable def S188 : Space := ⟨PiBase.Spaces.S188.S188, inferInstance⟩

end PiBase.Formal
