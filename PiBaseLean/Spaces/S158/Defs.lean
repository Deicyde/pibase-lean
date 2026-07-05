module

public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S158

/- Space 158: Unit interval [0,1].
See https://topology.pi-base.org/spaces/S000158.
The subspace $I = [0,1] = \{t \in \mathbb R : 0 \le t \le 1\}$ of ℝ (π-Base S25),
carrying the subspace topology induced from ℝ. -/

/-- The unit interval $[0,1]$ (pi-Base S158). -/
def S158 : Type := {t : ℝ // 0 ≤ t ∧ t ≤ 1}

instance S158_top : TopologicalSpace S158 := instTopologicalSpaceSubtype

end S158
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S158 as a bundled `Space` (carrier + topology). -/
noncomputable def S158 : Space := ⟨PiBase.Spaces.S158.S158, PiBase.Spaces.S158.S158_top⟩

end PiBase.Formal
