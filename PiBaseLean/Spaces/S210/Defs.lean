module

public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S210

/- Space 210: Interval [0,1).
See https://topology.pi-base.org/spaces/S000210.
The subspace topology on `{x : ℝ // 0 ≤ x ∧ x < 1}` inherited from ℝ (π-Base S25). -/

/-- The interval [0,1) (pi-Base S210). -/
def S210 : Type := {x : ℝ // 0 ≤ x ∧ x < 1}

instance : TopologicalSpace S210 := instTopologicalSpaceSubtype

end S210
end PiBase.Spaces
