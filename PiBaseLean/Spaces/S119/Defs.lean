module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S119

/- Space 119: Nested angles in the real plane.
See https://topology.pi-base.org/spaces/S000119.
The carrier is the union, over n = 1, 2, ..., of the segment from (0, 1) to
(n, 1/(n+1)) together with the half-line {(x, 1/(n+1)) : x ≤ n}, plus the line
y = 0, all sitting inside ℝ × ℝ; the topology is the subspace topology induced
from the product topology on ℝ × ℝ (pi-Base S176). -/

/-- The carrier of the nested-angles space: for each `n ≥ 1`, the segment from
`(0, 1)` to `(n, 1/(n+1))` together with the half-line `{(x, 1/(n+1)) : x ≤ n}`,
union the line `y = 0`. -/
def nestedAnglesCarrier : Set (ℝ × ℝ) :=
  (⋃ n : ℕ, ((segment ℝ ((0 : ℝ), (1 : ℝ)) ((n : ℝ) + 1, 1 / ((n : ℝ) + 2))) ∪
    {p : ℝ × ℝ | p.2 = 1 / ((n : ℝ) + 2) ∧ p.1 ≤ (n : ℝ) + 1})) ∪
  {p : ℝ × ℝ | p.2 = 0}

/-- Nested angles in the real plane (pi-Base S119). -/
def S119 : Type := nestedAnglesCarrier

instance S119_top : TopologicalSpace S119 := inferInstanceAs (TopologicalSpace nestedAnglesCarrier)

end S119
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S119 as a bundled `Space` (carrier + topology). -/
noncomputable def S119 : Space := ⟨PiBase.Spaces.S119.S119, PiBase.Spaces.S119.S119_top⟩

end PiBase.Formal
