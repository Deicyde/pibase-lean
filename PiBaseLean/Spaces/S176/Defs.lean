module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Constructions.SumProd

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S176

/- Space 176: Euclidean Plane ℝ².
See https://topology.pi-base.org/spaces/S000176.
The product topology on ℝ × ℝ. -/

/-- Euclidean Plane ℝ² (pi-Base S176). -/
def S176 : Type := ℝ × ℝ

instance S176_top : TopologicalSpace S176 := instTopologicalSpaceProd

end S176
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S176 as a bundled `Space` (carrier + topology). -/
noncomputable def S176 : Space := ⟨PiBase.Spaces.S176.S176, PiBase.Spaces.S176.S176_top⟩

end PiBase.Formal
