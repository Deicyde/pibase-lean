module

public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S175

/- Space 175: Radial plane.
See https://topology.pi-base.org/spaces/S000175.
Carrier ℝ × ℝ; `U` is open iff for every point `x ∈ U` and every line `L` through `x`,
`U ∩ L` is open in `L` with its Euclidean topology. We encode "every line through every
point" by ranging over all base points `x` and all nonzero directions `v`, coinducing the
topology of ℝ along the parametrization `t ↦ x + t • v` of the line through `x` with
direction `v`, and taking the supremum over all of these coinduced topologies. -/

/-- The radial plane (pi-Base S175): the set `ℝ × ℝ`. -/
def S175 : Type := ℝ × ℝ

/-- The radial (a.k.a. core) topology on `ℝ × ℝ`: the finest topology making every
line `t ↦ x + t • v` (for `x : ℝ × ℝ`, `v ≠ 0`) continuous from ℝ. -/
instance S175_top : TopologicalSpace S175 :=
  ⨆ (x : ℝ × ℝ) (v : ℝ × ℝ) (_ : v ≠ 0),
    TopologicalSpace.coinduced (fun t : ℝ => x + t • v) inferInstance

end S175
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S175 as a bundled `Space` (carrier + topology). -/
noncomputable def S175 : Space := ⟨PiBase.Spaces.S175.S175, PiBase.Spaces.S175.S175_top⟩

end PiBase.Formal
