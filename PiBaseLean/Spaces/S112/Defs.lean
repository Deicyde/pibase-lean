module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Constructions

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S112

/- Space 112: Nested rectangles in the real plane.
See https://topology.pi-base.org/spaces/S000112.
Let `L₁` be the line `x = 1`, `L₂` the line `x = -1`, and `R n` (for `n ≥ 1`) the boundary
of the rectangle centered at `(0, 0)` with height `2n` and width `2n / (n + 1)`. The carrier
is `L₁ ∪ L₂ ∪ ⋃ n ≥ 1, R n`, with the subspace topology inherited from `ℝ × ℝ`. -/

namespace S112

/-- The vertical line `x = 1` in `ℝ × ℝ`. -/
def L1 : Set (ℝ × ℝ) := {p | p.1 = 1}

/-- The vertical line `x = -1` in `ℝ × ℝ`. -/
def L2 : Set (ℝ × ℝ) := {p | p.1 = -1}

/-- The boundary of the rectangle centered at `(0, 0)` with height `2n` and width
`2n / (n + 1)`, i.e. `[-n/(n+1), n/(n+1)] × [-n, n]` minus its interior. -/
def R (n : ℕ) : Set (ℝ × ℝ) :=
  {p | |p.1| ≤ (n : ℝ) / (n + 1) ∧ |p.2| ≤ (n : ℝ) ∧
    (|p.1| = (n : ℝ) / (n + 1) ∨ |p.2| = (n : ℝ))}

/-- The carrier of the nested-rectangles space: the two lines `x = ±1` together with all
the rectangle boundaries `R n` for `n ≥ 1`. -/
def carrier : Set (ℝ × ℝ) := L1 ∪ L2 ∪ ⋃ n ≥ 1, R n

end S112

/-- Nested rectangles in the real plane (pi-Base S112). -/
def S112 : Type := S112.carrier

instance S112_top : TopologicalSpace S112 := instTopologicalSpaceSubtype

end S112
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S112 as a bundled `Space` (carrier + topology). -/
noncomputable def S112 : Space := ⟨PiBase.Spaces.S112.S112, PiBase.Spaces.S112.S112_top⟩

end PiBase.Formal
