module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Convex.Segment

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S116

/- Space 116: Infinite broom.
See https://topology.pi-base.org/spaces/S000116.
For each `n : ℕ` let `L n` be the closed line segment from `(0,0)` to `(1, 1/(n+1))`.
The carrier is `⋃ n, L n ∪ ((1/2, 1] × {0})`, a subset of `ℝ × ℝ` with the subspace
topology. -/

/-- For `n : ℕ`, the closed line segment in `ℝ × ℝ` from `(0,0)` to `(1, 1/(n+1))`. -/
def S116.L (n : ℕ) : Set (ℝ × ℝ) := segment ℝ ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), 1 / (n + 1 : ℝ))

/-- The "handle" of the broom: the half-open segment `(1/2, 1] × {0}`. -/
def S116.Handle : Set (ℝ × ℝ) := {p : ℝ × ℝ | 1 / 2 < p.1 ∧ p.1 ≤ 1 ∧ p.2 = 0}

/-- The carrier set of the infinite broom, as a subset of `ℝ × ℝ`. -/
def S116Set : Set (ℝ × ℝ) := (⋃ n : ℕ, S116.L n) ∪ S116.Handle

/-- Infinite broom (pi-Base S116). -/
def S116 : Type := S116Set

instance : TopologicalSpace S116 := inferInstanceAs (TopologicalSpace S116Set)

end S116
end PiBase.Spaces
