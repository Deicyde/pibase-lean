module

public import Mathlib.Topology.Constructions

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S184

/- Space 184: Sum of a pair of two-point indiscrete spaces.
See https://topology.pi-base.org/spaces/S000184.
The carrier `X = {0,1,2,3}` with topology `{∅, {0,1}, {2,3}, X}` is exactly the
topological sum `Fin 2 ⊕ Fin 2` of two copies of the indiscrete topology on a
two-point set (pi-Base S4): each summand is indiscrete, and the sum topology
(`instTopologicalSpaceSum`) makes a set open iff its restriction to each
summand is open, giving precisely `∅`, `{0,1}` (the left copy), `{2,3}`
(the right copy), and `X`. -/

/-- Sum of a pair of two-point indiscrete spaces (pi-Base S184). -/
def S184 : Type := Fin 2 ⊕ Fin 2

instance : TopologicalSpace (Fin 2) := ⊤

instance : TopologicalSpace S184 := instTopologicalSpaceSum

end S184
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S184 as a bundled `Space` (carrier + topology). -/
noncomputable def S184 : Space := ⟨PiBase.Spaces.S184.S184, inferInstance⟩

end PiBase.Formal
