module

public import Mathlib.Topology.Instances.Rat
public import Mathlib.Data.Real.Sqrt

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S67

/- Space 67: Irrational slope topology (a.k.a. Bing's connected countable space).
See https://topology.pi-base.org/spaces/S000067.
Carrier `X = {(x, y) : x, y ∈ ℚ, y ≥ 0}`; for a fixed irrational `θ > 0` (here `θ = √2`),
the local base at `(x, y)` is the family of sets `Nε(x, y) = {(x, y)} ∪ B(x - y/θ, ε)
∪ B(x + y/θ, ε)` for `ε > 0`, where `B(a, ε) = ((a - ε, a + ε) ∩ ℚ) × {0}` for real `a`.
We generate the topology from the union, over all points and all `ε > 0`, of these sets. -/

/-- The fixed irrational slope `θ = √2 > 0` used to define the topology. -/
noncomputable def S67.theta : ℝ := Real.sqrt 2

/-- `B a ε` is the set of rationals within `ε` of the real number `a`
(i.e. `(a - ε, a + ε) ∩ ℚ`, viewed inside the carrier as `B(a, ε) × {0}`). -/
def S67.B (a ε : ℝ) : Set ℚ := {q : ℚ | dist (q : ℝ) a < ε}

/-- Irrational slope topology (pi-Base S67). Carrier `X = ℚ × ℚ≥0`. -/
def S67 : Type := ℚ × {y : ℚ // 0 ≤ y}

/-- The basic neighbourhood `Nε(x, y)` of a point `(x, y)` in `X`, for `ε > 0`:
the point itself, together with the rationals on the `x`-axis near where the lines
of slope `±θ` through `(x, y)` cross it. -/
def S67.N (p : S67) (ε : ℝ) : Set S67 :=
  {p} ∪
    {q : S67 | q.2.val = 0 ∧ q.1 ∈ S67.B (p.1 - p.2.val / S67.theta) ε} ∪
    {q : S67 | q.2.val = 0 ∧ q.1 ∈ S67.B (p.1 + p.2.val / S67.theta) ε}

instance : TopologicalSpace S67 :=
  TopologicalSpace.generateFrom {s : Set S67 | ∃ p : S67, ∃ ε > (0 : ℝ), s = S67.N p ε}

end S67
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S67 as a bundled `Space` (carrier + topology). -/
noncomputable def S67 : Space := ⟨PiBase.Spaces.S67.S67, inferInstance⟩

end PiBase.Formal
