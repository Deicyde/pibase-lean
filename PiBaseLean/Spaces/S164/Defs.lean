module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S164

/- Space 164: Sum of singleton and two-point indiscrete space.
See https://topology.pi-base.org/spaces/S000164.
X = {a, b, c} with the topology {∅, {a, b}, {c}, X}, i.e. the topological sum of
the singleton {c} (S162) and the indiscrete two-point space {a, b} (S4). -/

/-- Sum of singleton and two-point indiscrete space (pi-Base S164). -/
def S164 : Type := Fin 3

instance : TopologicalSpace S164 :=
  TopologicalSpace.generateFrom {({0, 1} : Set (Fin 3)), ({2} : Set (Fin 3))}

instance : Finite S164 := inferInstanceAs (Finite (Fin 3))

instance : DecidableEq S164 := inferInstanceAs (DecidableEq (Fin 3))

end S164
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S164 as a bundled `Space` (carrier + topology). -/
noncomputable def S164 : Space := ⟨PiBase.Spaces.S164.S164, inferInstance⟩

end PiBase.Formal
