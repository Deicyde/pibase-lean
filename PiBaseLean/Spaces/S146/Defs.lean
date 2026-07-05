module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S146

/- Space 146: Countable product of rationals $\mathbb Q^\omega$.
See https://topology.pi-base.org/spaces/S000146.
The countable product of copies of ℚ (S27), carried by `ℕ → ℚ` with the product topology,
where each factor ℚ carries the subspace topology induced from ℝ. -/

/-- The countable product of rationals $\mathbb Q^\omega$ (pi-Base S146). -/
def S146 : Type := ℕ → ℚ

instance S146_top : TopologicalSpace S146 :=
  @Pi.topologicalSpace ℕ (fun _ => ℚ) (fun _ => TopologicalSpace.induced ((↑) : ℚ → ℝ) inferInstance)

end S146
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S146 as a bundled `Space` (carrier + topology). -/
noncomputable def S146 : Space := ⟨PiBase.Spaces.S146.S146, PiBase.Spaces.S146.S146_top⟩

end PiBase.Formal
