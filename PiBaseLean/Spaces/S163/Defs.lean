module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S163

/- Space 163: The Empty Space.
See https://topology.pi-base.org/spaces/S000163.
X = ∅ with its only valid topology {∅}. -/

/-- The Empty Space (pi-Base S163). -/
def S163 : Type := Empty

instance S163_top : TopologicalSpace S163 := TopologicalSpace.generateFrom {∅}

instance : IsEmpty S163 := inferInstanceAs (IsEmpty Empty)

end S163
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S163 as a bundled `Space` (carrier + topology). -/
noncomputable def S163 : Space := ⟨PiBase.Spaces.S163.S163, PiBase.Spaces.S163.S163_top⟩

end PiBase.Formal
