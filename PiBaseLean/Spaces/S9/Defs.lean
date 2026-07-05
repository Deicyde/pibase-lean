module

public import Mathlib.Topology.Order
public import Mathlib.Data.Real.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S9

/- Space 9: Particular point topology on ℝ.
See https://topology.pi-base.org/spaces/S000009.
A set is open iff it contains the particular point 0 or is empty. -/

/-- The particular point topology on ℝ, with particular point `0` (pi-Base S9). -/
def S9 : Type := ℝ

instance S9_top : TopologicalSpace S9 :=
  TopologicalSpace.generateFrom {s : Set S9 | s = ∅ ∨ (0 : ℝ) ∈ s}

end S9
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S9 as a bundled `Space` (carrier + topology). -/
noncomputable def S9 : Space := ⟨PiBase.Spaces.S9.S9, PiBase.Spaces.S9.S9_top⟩

end PiBase.Formal
