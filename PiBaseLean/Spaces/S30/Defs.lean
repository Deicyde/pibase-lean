module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S30

/- Space 30: Countable product of reals $\mathbb R^\omega$.
See https://topology.pi-base.org/spaces/S000030.
The countable product of copies of ℝ (S25), carried by `ℕ → ℝ` with the product topology. -/

/-- The countable product of reals $\mathbb R^\omega$ (pi-Base S30). -/
def S30 : Type := ℕ → ℝ

instance S30_top : TopologicalSpace S30 := Pi.topologicalSpace

end S30
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S30 as a bundled `Space` (carrier + topology). -/
noncomputable def S30 : Space := ⟨PiBase.Spaces.S30.S30, PiBase.Spaces.S30.S30_top⟩

end PiBase.Formal
