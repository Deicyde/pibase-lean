module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S170

/- Space 170: Circle $S^1$.
See https://topology.pi-base.org/spaces/S000170.
The subspace $\{x \in \mathbb{R}^2 : \|x\| = 1\}$ of the Euclidean plane (π-Base S176),
carrying the subspace topology induced from the Euclidean norm. -/

/-- The circle $S^1$ (pi-Base S170). -/
def S170 : Type := {x : EuclideanSpace ℝ (Fin 2) // ‖x‖ = 1}

instance : TopologicalSpace S170 := instTopologicalSpaceSubtype

end S170
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S170 as a bundled `Space` (carrier + topology). -/
noncomputable def S170 : Space := ⟨PiBase.Spaces.S170.S170, inferInstance⟩

end PiBase.Formal
