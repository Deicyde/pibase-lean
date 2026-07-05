module

public import Mathlib.Topology.Order
public import Mathlib.Data.Set.Finite.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S202

/- Space 202: Metric fan with `ω`-many spines.
See https://topology.pi-base.org/spaces/S000202.
Carrier `X = (ω × ω) ∪ {∞}`, represented as `Option (ℕ × ℕ)` (`∞ := none`). Every point
of `ω × ω` is isolated; basic open neighborhoods of `∞` are the sets obtained by
removing all but finitely-many *entire rows* of `ω × ω` (a row is `{m} × ω`). Compare
with the finer topology of the sequential fan (π-Base S131), whose neighborhoods of
`∞` only need to contain a tail of *every* row. -/

/-- The carrier of the metric fan with `ω`-many spines (pi-Base S202): the grid
`ω × ω` together with one extra point `∞` (represented as `none`). -/
def S202 : Type := Option (ℕ × ℕ)

/-- The generating open sets: each singleton `{(m,n)}` of the grid (making every grid
point isolated), together with the sets `U_F = {∞} ∪ {(m,n) : m ∉ F}` for each finite
`F ⊆ ℕ`, which form a neighborhood basis at `∞ = none` (a basic neighborhood of `∞`
contains all but finitely-many entire rows). -/
def S202.generators : Set (Set S202) :=
  -- Singletons of grid points, so every `(m, n)` is isolated.
  { s | ∃ p : ℕ × ℕ, s = {(some p : S202)} } ∪
  -- `U_F = {∞} ∪ {(m,n) : m ∉ F}`, for finite `F : Set ℕ`.
  { s | ∃ F : Set ℕ, F.Finite ∧
      s = {x : S202 | x = none ∨ ∃ p : ℕ × ℕ, x = some p ∧ p.1 ∉ F} }

instance : TopologicalSpace S202 := TopologicalSpace.generateFrom S202.generators

end S202
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S202 as a bundled `Space` (carrier + topology). -/
noncomputable def S202 : Space := ⟨PiBase.Spaces.S202.S202, inferInstance⟩

end PiBase.Formal
