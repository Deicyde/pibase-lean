module

public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Order.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S28

/- Space 28: Irrational numbers ℝ ∖ ℚ.
See https://topology.pi-base.org/spaces/S000028.
The subspace topology on `{x : ℝ // Irrational x}` inherited from ℝ (π-Base S25). -/

/-- The irrational numbers ℝ ∖ ℚ (pi-Base S28). -/
def S28 : Type := {x : ℝ // Irrational x}

instance : TopologicalSpace S28 := instTopologicalSpaceSubtype

end S28
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S28 as a bundled `Space` (carrier + topology). -/
noncomputable def S28 : Space := ⟨PiBase.Spaces.S28.S28, inferInstance⟩

end PiBase.Formal
