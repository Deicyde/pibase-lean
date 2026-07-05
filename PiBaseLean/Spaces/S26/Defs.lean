module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S26

/- Space 26: Cantor space 2^omega.
See https://topology.pi-base.org/spaces/S000026.
X = 2^omega with the product topology (each factor Bool/2 carrying the discrete topology). -/

/-- The Cantor space `2^ω` (pi-Base S26), realized as `ℕ → Bool` with the product topology. -/
def S26 : Type := ℕ → Bool

instance S26_top : TopologicalSpace S26 := Pi.topologicalSpace

end S26
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S26 as a bundled `Space` (carrier + topology). -/
noncomputable def S26 : Space := ⟨PiBase.Spaces.S26.S26, PiBase.Spaces.S26.S26_top⟩

end PiBase.Formal
