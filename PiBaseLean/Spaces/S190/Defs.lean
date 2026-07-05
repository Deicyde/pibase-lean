module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S190

/- Space 190: Indiscrete topology on {0, 1, 2}.
See https://topology.pi-base.org/spaces/S000190.
The only open sets are the whole set and the empty set. -/

/-- The indiscrete topology on `Fin 3` (pi-Base S190). -/
def S190 : Type := Fin 3

instance : TopologicalSpace S190 := ⊤

end S190
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S190 as a bundled `Space` (carrier + topology). -/
noncomputable def S190 : Space := ⟨PiBase.Spaces.S190.S190, inferInstance⟩

end PiBase.Formal
