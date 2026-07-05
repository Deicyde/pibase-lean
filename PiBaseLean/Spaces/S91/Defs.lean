module

public import Mathlib.Topology.Order
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

open Topology

namespace PiBase.Spaces

/- Space 91: Thomas plank.
See https://topology.pi-base.org/spaces/S000091.
Carrier: the "ground" row `L₀ = (0,1) × {0}` together with, for every `n : ℕ`,
a row `L_{n+1} = [0,1) × {1/(n+1)}`; a row point `(x, 1/(n+1))` with `x ≠ 0` is
isolated, `(0, 1/(n+1))` has the sets `{(0,1/(n+1))} ∪ ((x, 1/(n+1)) with x ∉ F)`
for `F` finite as neighborhoods, and `(x, 0) ∈ L₀` has the sets
`U_i(x,0) = {(x,0)} ∪ {(x, 1/n) | n > i}` as neighborhoods. -/

/-- The carrier of the Thomas plank (pi-Base S91): the union of
`L₀ = {(x, 0) : x ∈ (0,1)}` with, for each `n : ℕ`, the row
`L_{n+1} = {(x, 1/(n+1)) : x ∈ [0,1)}`. -/
def S91 : Type :=
  {p : ℝ × ℝ // (p.2 = 0 ∧ p.1 ∈ Set.Ioo (0 : ℝ) 1) ∨
    ∃ n : ℕ, p.2 = 1 / (n + 1 : ℝ) ∧ p.1 ∈ Set.Ico (0 : ℝ) 1}

/-- The generating open sets for the Thomas plank topology:
isolated points of the rows `L_{n+1}` away from `x = 0`, cofinite-in-row
neighborhoods of the row-endpoints `(0, 1/(n+1))`, and the "tail" basis
neighborhoods `U_i(x,0)` of the ground-row points `(x,0)`. -/
def S91.generators : Set (Set S91) :=
  { s | ∃ p : S91, p.1.2 ≠ 0 ∧ p.1.1 ≠ 0 ∧ s = {p} } ∪
  { s | ∃ (n : ℕ) (F : Set ℝ), F.Finite ∧
      s = {p : S91 | p.1.2 = 1 / (n + 1 : ℝ) ∧ p.1.1 ∉ F} } ∪
  { s | ∃ (x : ℝ) (_ : x ∈ Set.Ioo (0 : ℝ) 1) (i : ℕ),
      s = {p : S91 | p.1.1 = x ∧ (p.1.2 = 0 ∨ ∃ n ≥ i, p.1.2 = 1 / (n + 1 : ℝ))} }

instance : TopologicalSpace S91 := TopologicalSpace.generateFrom S91.generators

end PiBase.Spaces
