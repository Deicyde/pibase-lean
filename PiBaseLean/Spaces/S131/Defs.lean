module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S131

/- Space 131: Sequential fan with `ω`-many spines.
See https://topology.pi-base.org/spaces/S000131.
Carrier `X = (ω × ω) ∪ {∞}`, represented as `Option (ℕ × ℕ)` (`∞ := none`). Every point
of `ω × ω` is isolated; basic open neighborhoods of `∞` are the sets
`U_f = {∞} ∪ {(m,n) : n ≥ f(m)}` for an arbitrary `f : ω → ω`. -/

/-- The carrier of the sequential fan with `ω`-many spines (pi-Base S131): the grid
`ω × ω` together with one extra point `∞` (represented as `none`). -/
def S131 : Type := Option (ℕ × ℕ)

/-- The generating open sets: each singleton `{(m,n)}` of the grid (making every grid
point isolated), together with the tail sets `U_f = {∞} ∪ {(m,n) : n ≥ f(m)}` for each
`f : ℕ → ℕ`, which form a neighborhood basis at `∞ = none`. -/
def S131.generators : Set (Set S131) :=
  -- Singletons of grid points, so every `(m, n)` is isolated.
  { s | ∃ p : ℕ × ℕ, s = {(some p : S131)} } ∪
  -- `U_f = {∞} ∪ {(m,n) : n ≥ f(m)}`, for `f : ℕ → ℕ`.
  { s | ∃ f : ℕ → ℕ,
      s = {x : S131 | x = none ∨ ∃ p : ℕ × ℕ, x = some p ∧ f p.1 ≤ p.2} }

instance : TopologicalSpace S131 := TopologicalSpace.generateFrom S131.generators

end S131
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S131 as a bundled `Space` (carrier + topology). -/
noncomputable def S131 : Space := ⟨PiBase.Spaces.S131.S131, inferInstance⟩

end PiBase.Formal
