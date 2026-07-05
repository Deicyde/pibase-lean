module

public import Mathlib.Topology.Constructions

public import PiBaseLean.Spaces.Bundled.Defs

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

instance S15_top : TopologicalSpace S15 := inferInstanceAs (TopologicalSpace (CofiniteTopology ℕ))

end S15
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S15 as a bundled `Space` (carrier + topology). -/
noncomputable def S15 : Space := ⟨PiBase.Spaces.S15.S15, PiBase.Spaces.S15.S15_top⟩

end PiBase.Formal
