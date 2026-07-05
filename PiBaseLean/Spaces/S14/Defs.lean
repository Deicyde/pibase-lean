module

public import Mathlib.Topology.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S14

/- Space 14: Either-Or Topology.
See https://topology.pi-base.org/spaces/S000014.
Carrier `X = [-1, 1] ⊆ ℝ`; a set `U ⊆ X` is open iff `0 ∉ U` or `(-1, 1) ⊆ U`. -/

/-- Either-Or Topology (pi-Base S14), on the interval `[-1, 1] ⊆ ℝ`. -/
def S14 : Type := ↥(Set.Icc (-1 : ℝ) 1)

instance S14_top : TopologicalSpace S14 :=
  TopologicalSpace.generateFrom
    {s : Set S14 |
      (∀ x ∈ s, (x.val : ℝ) ≠ 0) ∨
        ∀ x : S14, (x.val : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 → x ∈ s}

end S14
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S14 as a bundled `Space` (carrier + topology). -/
noncomputable def S14 : Space := ⟨PiBase.Spaces.S14.S14, PiBase.Spaces.S14.S14_top⟩

end PiBase.Formal
