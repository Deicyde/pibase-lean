module

public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S73

/- Space 73: Simplified Arens square.
See https://topology.pi-base.org/spaces/S000073.
Carrier `X = (0,1)² ∪ {(0,0),(1,0)} ⊆ ℝ × ℝ`; the open square `(0,1)²` keeps its
Euclidean subspace topology, and the two extra corner points `(0,0)`, `(1,0)`
get the local bases `Uₙ(0,0) = {(0,0)} ∪ {(x,y) : x < 1/2, y < 1/n}` and
`Uₙ(1,0) = {(1,0)} ∪ {(x,y) : 1/2 < x, y < 1/n}`. -/

/-- The carrier of the simplified Arens square: the open unit square together
with the two corner points `(0,0)` and `(1,0)`. -/
def S73 : Type := ↥((Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) ∪ {((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))})

/-- The generating open sets: every Euclidean-open subset of `ℝ × ℝ` restricted
to `X` (giving `(0,1)²` its subspace topology), together with the local-basis
sets `Uₙ(0,0)` and `Uₙ(1,0)` at the two corner points, for each `n ≥ 1`. -/
instance : TopologicalSpace S73 :=
  TopologicalSpace.generateFrom
    ({s : Set S73 | ∃ u : Set (ℝ × ℝ), IsOpen u ∧ s = {x : S73 | (x.val : ℝ × ℝ) ∈ u}} ∪
      {s : Set S73 | ∃ n : ℕ, 1 ≤ n ∧
        s = {x : S73 | (x.val : ℝ × ℝ) = ((0 : ℝ), (0 : ℝ)) ∨
          ((x.val : ℝ × ℝ).1 < 1 / 2 ∧ (x.val : ℝ × ℝ).2 < 1 / (n : ℝ))}} ∪
      {s : Set S73 | ∃ n : ℕ, 1 ≤ n ∧
        s = {x : S73 | (x.val : ℝ × ℝ) = ((1 : ℝ), (0 : ℝ)) ∨
          ((1 / 2 : ℝ) < (x.val : ℝ × ℝ).1 ∧ (x.val : ℝ × ℝ).2 < 1 / (n : ℝ))}})

end S73
end PiBase.Spaces
