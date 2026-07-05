module

public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Order

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S3

/- Space 3: Discrete topology on ℝ.
See https://topology.pi-base.org/spaces/S000003.
The carrier is ℝ, topologized with the discrete topology `⊥` (every subset is open). -/

/-- Discrete topology on ℝ (pi-Base S3). -/
def S3 : Type := ℝ

instance : TopologicalSpace S3 := ⊥

instance : DiscreteTopology S3 := discreteTopology_bot S3

end S3
end PiBase.Spaces
