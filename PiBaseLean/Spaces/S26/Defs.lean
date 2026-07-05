module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S26

/- Space 26: Cantor space 2^omega.
See https://topology.pi-base.org/spaces/S000026.
X = 2^omega with the product topology (each factor Bool/2 carrying the discrete topology). -/

/-- The Cantor space `2^ω` (pi-Base S26), realized as `ℕ → Bool` with the product topology. -/
def S26 : Type := ℕ → Bool

instance : TopologicalSpace S26 := Pi.topologicalSpace

end S26
end PiBase.Spaces
