module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S169

/- Space 169: Sphere $S^2$.
See https://topology.pi-base.org/spaces/S000169.
The subspace `{x ∈ ℝ³ : ‖x‖ = 1}` of Euclidean space ℝ³, with the subspace topology
induced from the ambient Euclidean metric. -/

/-- Sphere $S^2$ (pi-Base S169). -/
def S169 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

instance S169_top : TopologicalSpace S169 :=
  TopologicalSpace.induced (Subtype.val : S169 → EuclideanSpace ℝ (Fin 3)) inferInstance

end S169
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S169 as a bundled `Space` (carrier + topology). -/
noncomputable def S169 : Space := ⟨PiBase.Spaces.S169.S169, PiBase.Spaces.S169.S169_top⟩

end PiBase.Formal
