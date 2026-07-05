module

public import Mathlib.Topology.Order
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S189

/- Space 189: Discrete topology on {0,1,2}.
See https://topology.pi-base.org/spaces/S000189.
The carrier is the three-element set X = {0, 1, 2}, with every subset of X declared open. -/

/-- Discrete topology on `{0, 1, 2}` (pi-Base S189). -/
def S189 : Type := Fin 3

instance : TopologicalSpace S189 := ⊥

instance : Finite S189 := inferInstanceAs (Finite (Fin 3))
instance : DecidableEq S189 := inferInstanceAs (DecidableEq (Fin 3))
instance : DiscreteTopology S189 := ⟨rfl⟩
instance : CompactSpace S189 := Finite.compactSpace

end S189
end PiBase.Spaces
