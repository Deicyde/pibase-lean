module

public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S50

/- Space 50: ℚ extended by a focal point.
See https://topology.pi-base.org/spaces/S000050.
Carrier `X = ℚ ∪ {∞}` modeled as `Option ℚ` (`∞ := none`). The open sets are generated
from the opens of ℚ (Euclidean subspace topology, pulled back along `some`), each of which
omits `none`; `generateFrom` always makes `univ` open, and since unions/finite intersections
of sets omitting `none` still omit it, `univ` is the *only* open set containing `none` —
i.e. the only neighborhood of the focal point `∞` is all of `X`. -/

/-- ℚ extended by a focal point (pi-Base S50). -/
def S50 : Type := Option ℚ

instance S50_top : TopologicalSpace S50 :=
  TopologicalSpace.generateFrom
    {s : Set S50 | none ∉ s ∧ IsOpen[TopologicalSpace.induced ((↑) : ℚ → ℝ) inferInstance]
      (Option.some ⁻¹' s : Set ℚ)}

end S50
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S50 as a bundled `Space` (carrier + topology). -/
noncomputable def S50 : Space := ⟨PiBase.Spaces.S50.S50, PiBase.Spaces.S50.S50_top⟩

end PiBase.Formal
