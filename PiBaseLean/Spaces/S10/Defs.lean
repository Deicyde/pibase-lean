module

public import Mathlib.Topology.Order

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S10

/- Space 10: Sierpinski space.
See https://topology.pi-base.org/spaces/S000010.
The carrier `X = {0, 1}` topologized with open sets `{∅, {0}, X}`, generated from the
single subbasic set `{0}` (the particular-point topology at `0` on a two-point set). -/

/-- Sierpinski space (pi-Base S10). -/
def S10 : Type := Fin 2

instance : TopologicalSpace S10 :=
  TopologicalSpace.generateFrom {({0} : Set (Fin 2))}

end S10
end PiBase.Spaces
