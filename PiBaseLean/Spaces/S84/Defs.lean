module

public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S84

/- Space 84: Line with countably many origins.
See https://topology.pi-base.org/spaces/S000084.
Carrier `X = {p : ℝ × ℕ // p.1 = 0 ∨ p.2 = 0}`: a point `x ≠ 0` is represented
uniquely as `(x, 0)`, while `0` is replaced by countably many origins `0_α = (0, α)`,
one for each `α : ℕ`. Basic open sets are, for each Euclidean-open `U : Set ℝ` and
each `α : ℕ`, the set `(U \ {0}) ∪ ({0_α} if 0 ∈ U else ∅)` — i.e. `U` with the
origin (if present) replaced by the single origin `0_α`. -/

/-- The carrier of the line with countably many origins (pi-Base S84): pairs
`(x, α) : ℝ × ℕ` with `x = 0 ∨ α = 0`, so away from `x = 0` only `α = 0` occurs
(a single copy of each nonzero real), while at `x = 0` every `α : ℕ` occurs
(the countably many origins). -/
def S84 : Type := {p : ℝ × ℕ // p.1 = 0 ∨ p.2 = 0}

/-- Basic open sets: for `U` open in `ℝ` and `α : ℕ`, the set of points `(x, β)`
with `x ∈ U` and either `x ≠ 0` (any copy) or `β = α` (the `α`-th origin). This is
`U` with its origin, if any, specialized to the single origin `0_α`. -/
instance : TopologicalSpace S84 :=
  TopologicalSpace.generateFrom
    {s : Set S84 | ∃ (U : Set ℝ), IsOpen U ∧ ∃ α : ℕ,
      s = {p : S84 | p.val.1 ∈ U ∧ (p.val.1 ≠ 0 ∨ p.val.2 = α)}}

end S84
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S84 as a bundled `Space` (carrier + topology). -/
noncomputable def S84 : Space := ⟨PiBase.Spaces.S84.S84, inferInstance⟩

end PiBase.Formal
