module

public import Mathlib.Topology.Order

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

instance : TopologicalSpace S193 := ⊤

end S193
end PiBase.Spaces
