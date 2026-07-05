module

public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S27

/- Space 27: Rational numbers ℚ.
See https://topology.pi-base.org/spaces/S000027.
Carrier `X = ℚ`, with the subspace topology induced from the Euclidean reals ℝ
(pi-Base S25) via the inclusion `(↑) : ℚ → ℝ`. -/

/-- Rational numbers ℚ (pi-Base S27), with the subspace topology from ℝ. -/
def S27 : Type := ℚ

instance S27_top : TopologicalSpace S27 :=
  TopologicalSpace.induced ((↑) : ℚ → ℝ) inferInstance

end S27
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S27 as a bundled `Space` (carrier + topology). -/
noncomputable def S27 : Space := ⟨PiBase.Spaces.S27.S27, PiBase.Spaces.S27.S27_top⟩

end PiBase.Formal
