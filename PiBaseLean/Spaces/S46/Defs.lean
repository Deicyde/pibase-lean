module

public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S46

/- Space 46: Interlocking interval topology.
See https://topology.pi-base.org/spaces/S000046.
Carrier `X = (0, ∞) \ ℤ ⊆ ℝ`; topologized by taking, for each `n ≥ 1`, the set
`Sₙ = (0, 1/n) ∪ (n, n+1)` as a subbasic open set. -/

/-- Interlocking interval topology (pi-Base S46), on the carrier
`(0, ∞) \ ℤ ⊆ ℝ`. -/
def S46 : Type := ↥(Set.Ioi (0 : ℝ) \ Set.range ((↑) : ℤ → ℝ))

/-- The subbasic sets `Sₙ = (0, 1/n) ∪ (n, n+1)`, `n ≥ 1`, restricted to `S46`. -/
instance : TopologicalSpace S46 :=
  TopologicalSpace.generateFrom
    {s : Set S46 | ∃ n : ℕ, 1 ≤ n ∧
      s = {x : S46 | (x.val : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)) ∪ Set.Ioo (n : ℝ) (n + 1)}}

end S46
end PiBase.Spaces
