module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.NumberTheory.Real.Irrational

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S130

/- Space 130: Tangora's connected space.
See https://topology.pi-base.org/spaces/S000130.
Carrier `X = ℝ`, partitioned into `A` (the dyadic rationals `m / 2ⁿ`), `B` (the remaining
rationals `ℚ \ A`), and `C` (the irrationals). The topology extends the usual topology on
`ℝ` by also declaring `A` and `B` open, together with every set `{c} ∪ ((c - δ, c + δ) \ C)`
for `c ∈ C` and `δ > 0`. We generate the topology from the union of these three families of
generating sets: the standard opens of `ℝ`, `{A, B}`, and the punctured-neighbourhood sets
around irrationals. -/

/-- The dyadic rationals `A = {m / 2ⁿ : m ∈ ℤ, n ∈ ℕ} ⊂ ℚ` (pi-Base S130). -/
def S130.A : Set ℝ := {x : ℝ | ∃ (m : ℤ) (n : ℕ), x = (m : ℝ) / 2 ^ n}

/-- The remaining rationals `B = ℚ \ A` (pi-Base S130). -/
def S130.B : Set ℝ := {x : ℝ | ∃ q : ℚ, x = (q : ℝ)} \ S130.A

/-- The irrationals `C = ℝ \ ℚ` (pi-Base S130). -/
def S130.C : Set ℝ := {x : ℝ | Irrational x}

/-- The punctured neighbourhood `{c} ∪ ((c - δ, c + δ) \ C)` of an irrational point `c`,
for `δ > 0`: `c` together with the non-irrational (i.e. rational) points of the usual
`δ`-ball around it. -/
def S130.N (c : ℝ) (δ : ℝ) : Set ℝ := {c} ∪ (Set.Ioo (c - δ) (c + δ) \ S130.C)

/-- The carrier of Tangora's connected space (pi-Base S130): the reals. -/
def S130 : Type := ℝ

/-- The generating sets: the standard opens of `ℝ`, the two dense pieces `A` and `B`,
and the punctured neighbourhoods `N c δ` of irrational points. -/
def S130.generators : Set (Set S130) :=
  {s : Set ℝ | IsOpen s} ∪ {S130.A, S130.B} ∪
    {s : Set ℝ | ∃ c : ℝ, Irrational c ∧ ∃ δ > (0 : ℝ), s = S130.N c δ}

instance S130_top : TopologicalSpace S130 := TopologicalSpace.generateFrom S130.generators

end S130
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S130 as a bundled `Space` (carrier + topology). -/
noncomputable def S130 : Space := ⟨PiBase.Spaces.S130.S130, PiBase.Spaces.S130.S130_top⟩

end PiBase.Formal
