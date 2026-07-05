module

public import Mathlib.Topology.Order
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Rat.Cast.Defs

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S75

/- Space 75: Rational tangent disc topology.
See https://topology.pi-base.org/spaces/S000075.
Carrier `X = {(x, y) : y > 0} ∪ {(q, 0) : q ∈ ℚ} ⊆ ℝ × ℝ`: the open upper half
plane together with the rational points on the `x`-axis. Points of the open
upper half plane keep their usual Euclidean neighborhoods; a rational boundary
point `(q, 0)` has as a local neighborhood base the sets `{(q, 0)} ∪ D`, where
`D` is an open disc in the upper half plane tangent to the `x`-axis at `(q, 0)`
(center `(q, r)`, radius `r > 0`). This is the metrizable-tangent-disc
subspace of the Niemytzki plane (S74) obtained by keeping only countably many
(the rational) boundary points. -/

/-- The carrier of the rational tangent disc topology (pi-Base S75): the open
upper half plane together with the rational points on the `x`-axis. -/
def S75 : Type :=
  ↥{p : ℝ × ℝ | 0 < p.2 ∨ (p.2 = 0 ∧ ∃ q : ℚ, (q : ℝ) = p.1)}

/-- The generating subbasis: every Euclidean-open subset of `ℝ × ℝ` restricted
to `X` (giving the open upper half plane its usual Euclidean neighborhoods),
together with the tangent-disc local basis `{(q, 0)} ∪ D` at each rational
boundary point `q : ℚ`, where `D` is the open disc of center `(q, r)` and
radius `r > 0` (so `D` is tangent to the `x`-axis at `(q, 0)`). -/
instance S75_top : TopologicalSpace S75 :=
  TopologicalSpace.generateFrom
    ({s : Set S75 | ∃ u : Set (ℝ × ℝ), IsOpen u ∧ s = {x : S75 | (x.val : ℝ × ℝ) ∈ u}} ∪
      {s : Set S75 | ∃ q : ℚ, ∃ r : ℝ, 0 < r ∧
        s = {x : S75 | (x.val : ℝ × ℝ) = ((q : ℝ), (0 : ℝ)) ∨
          ((x.val : ℝ × ℝ).1 - (q : ℝ)) ^ 2 + ((x.val : ℝ × ℝ).2 - r) ^ 2 < r ^ 2}})

end S75
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S75 as a bundled `Space` (carrier + topology). -/
noncomputable def S75 : Space := ⟨PiBase.Spaces.S75.S75, PiBase.Spaces.S75.S75_top⟩

end PiBase.Formal
