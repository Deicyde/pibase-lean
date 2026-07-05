module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S193

/- Space 193: Indiscrete topology on $\omega$.
See https://topology.pi-base.org/spaces/S000193.
Carrier `ω = ℕ`, a countably infinite set; the only open sets are `∅` and the
whole space, i.e. the indiscrete topology `⊤`. -/

/-- Indiscrete topology on `ω` (pi-Base S193). -/
def S193 : Type := ℕ

instance S193_top : TopologicalSpace S193 := ⊤

end S193
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S193 as a bundled `Space` (carrier + topology). -/
noncomputable def S193 : Space := ⟨PiBase.Spaces.S193.S193, PiBase.Spaces.S193.S193_top⟩

end PiBase.Formal
