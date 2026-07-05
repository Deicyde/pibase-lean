module

public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S113

/- Space 113: Topologist's sine curve.
See https://topology.pi-base.org/spaces/S000113.
Carrier `X = {(x, sin (1 / x)) : x ∈ (0, 1]} ∪ {(0, 0)} ⊆ ℝ²`, with the subspace
topology inherited from `ℝ²` (with its usual product topology). -/

/-- Topologist's sine curve (pi-Base S113), on the subset
`{(x, sin (1 / x)) : x ∈ (0, 1]} ∪ {(0, 0)}` of `ℝ × ℝ`. -/
def S113 : Type :=
  ↥({p : ℝ × ℝ | ∃ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ∧ p = (x, Real.sin (1 / x))} ∪ {(0, 0)})

instance : TopologicalSpace S113 := instTopologicalSpaceSubtype

end S113
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S113 as a bundled `Space` (carrier + topology). -/
noncomputable def S113 : Space := ⟨PiBase.Spaces.S113.S113, inferInstance⟩

end PiBase.Formal
