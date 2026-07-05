module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S120

/- Space 120: Infinite cage.
See https://topology.pi-base.org/spaces/S000120.
For each integer `n ≥ 1`, let
`A n = {(1/n, y, 0) : 0 ≤ y ≤ 3n}`,
`B n = {(0, y, 0) : 2n - 1/2 ≤ y ≤ 2n + 1/2}` and
`C n = {(x, y, z) : 0 ≤ x ≤ 1/n, y = 2n, z = x(1/n - x)}`.
The Infinite Cage is `X = ⋃ n ≥ 1, (A n ∪ B n ∪ C n) ⊆ ℝ × ℝ × ℝ`, with the
subspace topology inherited from `ℝ × ℝ × ℝ` (with its usual product topology). -/

/-- The `n`-th "rung post": `A n = {(1/n, y, 0) : 0 ≤ y ≤ 3n}` (pi-Base S120). -/
def S120.A (n : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {p : ℝ × ℝ × ℝ | p.1 = 1 / (n : ℝ) ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ 3 * (n : ℝ) ∧ p.2.2 = 0}

/-- The `n`-th "spine segment": `B n = {(0, y, 0) : 2n - 1/2 ≤ y ≤ 2n + 1/2}`
(pi-Base S120). -/
def S120.B (n : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {p : ℝ × ℝ × ℝ |
    p.1 = 0 ∧ 2 * (n : ℝ) - 1 / 2 ≤ p.2.1 ∧ p.2.1 ≤ 2 * (n : ℝ) + 1 / 2 ∧ p.2.2 = 0}

/-- The `n`-th "rung arc": `C n = {(x, y, z) : 0 ≤ x ≤ 1/n, y = 2n, z = x(1/n - x)}`
(pi-Base S120). -/
def S120.C (n : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {p : ℝ × ℝ × ℝ |
    0 ≤ p.1 ∧ p.1 ≤ 1 / (n : ℝ) ∧ p.2.1 = 2 * (n : ℝ) ∧ p.2.2 = p.1 * (1 / (n : ℝ) - p.1)}

/-- The Infinite Cage (pi-Base S120), as the subset
`⋃ n ≥ 1, (A n ∪ B n ∪ C n)` of `ℝ × ℝ × ℝ`. -/
def S120 : Type :=
  ↥(⋃ n ∈ {n : ℕ | 1 ≤ n}, (S120.A n ∪ S120.B n ∪ S120.C n))

instance : TopologicalSpace S120 := instTopologicalSpaceSubtype

end S120
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S120 as a bundled `Space` (carrier + topology). -/
noncomputable def S120 : Space := ⟨PiBase.Spaces.S120.S120, inferInstance⟩

end PiBase.Formal
