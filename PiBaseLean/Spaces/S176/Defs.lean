module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S176

/- Space 176: Euclidean Plane ℝ².
See https://topology.pi-base.org/spaces/S000176.
The product topology on ℝ × ℝ. -/

/-- Euclidean Plane ℝ² (pi-Base S176). -/
def S176 : Type := ℝ × ℝ

instance : TopologicalSpace S176 := instTopologicalSpaceProd

end S176
end PiBase.Spaces
