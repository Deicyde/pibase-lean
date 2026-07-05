module

public import Mathlib.Topology.Order
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Data.Real.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S94

/- Space 94: Strong parallel line topology.
See https://topology.pi-base.org/spaces/S000094.
Carrier: `A = {(x,0) : 0 < x ≤ 1}` together with `B = {(x,1) : 0 ≤ x < 1}`, with a basis
of sets `V = {(x,1) : a ≤ x < b}` (inside `B`) and `U = {(x,0) : a < x ≤ b} ∪ {(x,1) : a < x < b}`
(straddling both rows). -/

/-- The carrier of the strong parallel line topology (pi-Base S94): the union of
`A = {(x,0) : 0 < x ≤ 1}` and `B = {(x,1) : 0 ≤ x < 1}`, as a subset of the plane. -/
def S94 : Type :=
  {p : ℝ × ℝ // (p.2 = 0 ∧ p.1 ∈ Set.Ioc (0 : ℝ) 1) ∨ (p.2 = 1 ∧ p.1 ∈ Set.Ico (0 : ℝ) 1)}

/-- The generating open sets for the strong parallel line topology: the row-`B` intervals
`V = {(x,1) : a ≤ x < b}` and the straddling sets `U = {(x,0) : a < x ≤ b} ∪ {(x,1) : a < x < b}`. -/
def S94.generators : Set (Set S94) :=
  { s | ∃ a b : ℝ, s = {p : S94 | p.1.2 = 1 ∧ a ≤ p.1.1 ∧ p.1.1 < b} } ∪
  { s | ∃ a b : ℝ, s = {p : S94 | (p.1.2 = 0 ∧ a < p.1.1 ∧ p.1.1 ≤ b) ∨
      (p.1.2 = 1 ∧ a < p.1.1 ∧ p.1.1 < b)} }

instance S94_top : TopologicalSpace S94 := TopologicalSpace.generateFrom S94.generators

end S94
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S94 as a bundled `Space` (carrier + topology). -/
noncomputable def S94 : Space := ⟨PiBase.Spaces.S94.S94, PiBase.Spaces.S94.S94_top⟩

end PiBase.Formal
