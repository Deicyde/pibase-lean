module

public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S225

/- Space 225: Closed upper half-plane ℝ²₊.
See https://topology.pi-base.org/spaces/S000225.
The subspace {(x, y) ∈ ℝ² : y ≥ 0} of the Euclidean plane ℝ², with the subspace
topology induced from the product topology on ℝ × ℝ. -/

/-- The closed upper half-plane `{(x, y) ∈ ℝ² : y ≥ 0}` (pi-Base S225). -/
def S225 : Type := {p : ℝ × ℝ // 0 ≤ p.2}

instance : TopologicalSpace S225 :=
  inferInstanceAs (TopologicalSpace {p : ℝ × ℝ // 0 ≤ p.2})

end S225
end PiBase.Spaces
