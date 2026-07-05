module

public import Mathlib.Topology.Order
public import Mathlib.Topology.Compactness.Compact

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S1

/- Space 1: Discrete topology on {0, 1}.
See https://topology.pi-base.org/spaces/S000001.
All subsets of the two-point set are open. -/

/-- The discrete topology on `Fin 2` (pi-Base S1). -/
def S1 : Type := Fin 2

instance S1_top : TopologicalSpace S1 := ⊥

instance : Finite S1 := inferInstanceAs (Finite (Fin 2))
instance : DecidableEq S1 := inferInstanceAs (DecidableEq (Fin 2))
instance : DiscreteTopology S1 := discreteTopology_bot (Fin 2)
instance : CompactSpace S1 := Finite.compactSpace

end S1
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S1 as a bundled `Space` (carrier + topology). -/
noncomputable def S1 : Space := ⟨PiBase.Spaces.S1.S1, PiBase.Spaces.S1.S1_top⟩

end PiBase.Formal
