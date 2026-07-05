module

public import Mathlib.Topology.Order
public import Mathlib.Data.Countable.Defs

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S2

/- Space 2: Discrete topology on $\omega$.
See https://topology.pi-base.org/spaces/S000002.
All subsets of the countably infinite set `ℕ` are open. -/

/-- The discrete topology on `ℕ` (pi-Base S2). -/
def S2 : Type := ℕ

instance S2_top : TopologicalSpace S2 := ⊥

instance : Infinite S2 := inferInstanceAs (Infinite ℕ)
instance : Countable S2 := inferInstanceAs (Countable ℕ)
instance : DecidableEq S2 := inferInstanceAs (DecidableEq ℕ)
instance : DiscreteTopology S2 := discreteTopology_bot ℕ

end S2
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S2 as a bundled `Space` (carrier + topology). -/
noncomputable def S2 : Space := ⟨PiBase.Spaces.S2.S2, PiBase.Spaces.S2.S2_top⟩

end PiBase.Formal
