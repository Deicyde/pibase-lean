module

public import Mathlib.Topology.Constructions

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S15

/- Space 15: Cofinite topology on $\omega$.
See https://topology.pi-base.org/spaces/S000015.
The carrier is $\omega = \mathbb{N}$; a set $U$ is open iff $U = \emptyset$ or its
complement is finite -- exactly Mathlib's `CofiniteTopology`. -/

/-- Cofinite topology on $\omega$ (pi-Base S15). -/
def S15 : Type := CofiniteTopology ℕ

instance : TopologicalSpace S15 := inferInstanceAs (TopologicalSpace (CofiniteTopology ℕ))

end S15
end PiBase.Spaces
