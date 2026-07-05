module

public import Mathlib.Topology.Order
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Real.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S17

/- Space 17: Cocountable topology on ℝ.
See https://topology.pi-base.org/spaces/S000017.
On `X = ℝ`, a set is open iff it is empty or its complement is countable. -/

/-- Cocountable topology on ℝ (pi-Base S17). -/
def S17 : Type := ℝ

instance : TopologicalSpace S17 :=
  TopologicalSpace.generateFrom {s : Set S17 | s = ∅ ∨ sᶜ.Countable}

end S17
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S17 as a bundled `Space` (carrier + topology). -/
noncomputable def S17 : Space := ⟨PiBase.Spaces.S17.S17, inferInstance⟩

end PiBase.Formal
