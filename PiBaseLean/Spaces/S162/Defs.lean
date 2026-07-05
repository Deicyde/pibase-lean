module

public import Mathlib.Topology.Order

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S162

/- Space 162: The Singleton.
See https://topology.pi-base.org/spaces/S000162.
X = {x} with its only valid topology {∅, X}. -/

/-- The Singleton (pi-Base S162). -/
def S162 : Type := Unit

instance : TopologicalSpace S162 := (⊤ : TopologicalSpace Unit)

end S162
end PiBase.Spaces
