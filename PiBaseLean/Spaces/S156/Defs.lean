module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S156

/- Space 156: Arens space (aliased $S_2$).
See https://topology.pi-base.org/spaces/S000156.
Let `X = ω ∪ {∞}` be the one-point compactification of the countable discrete
space (pi-Base S20). Arens space is the minimal topology on `(X × ω) ∪ {∞'}`
for which `({∞} × ω) ∪ {∞'}` is homeomorphic to `X`: every grid point `(n, m)`
with `n, m : ℕ` is isolated; a set containing `(∞, m)` is a neighborhood of it
iff it contains all but finitely many grid points `(n, m)` in column `m`; and a
set containing `∞'` is a neighborhood of it iff, for all but finitely many
columns `m`, it contains `(∞, m)` together with all but finitely many grid
points `(n, m)` in column `m`. We model `X` as `Option ℕ` (`none = ∞`) and the
extra point `∞'` via an outer `Option`, giving carrier `Option (Option ℕ × ℕ)`
with `none = ∞'` and `some (x, m)` the point `(x, m) ∈ X × ω`. -/

/-- Arens space (pi-Base S156). The carrier `Option (Option ℕ × ℕ)`: `none` is
the extra point `∞'`, and `some (x, m)` is the point `(x, m)` of
`(ω ∪ {∞}) × ω`, with `x = none` reading as `∞` in that copy of `ω ∪ {∞}`. -/
def S156 : Type := Option (Option ℕ × ℕ)

/-- The generating open sets: every singleton grid point `(n, m)` with
`n, m : ℕ`; for each column `m`, every set containing `(∞, m)` that is
cofinite in that column; and every set containing `∞'` that, for all but
finitely many columns `m`, contains `(∞, m)` and is cofinite in column `m`. -/
instance : TopologicalSpace S156 :=
  TopologicalSpace.generateFrom
    ({s : Set S156 | ∃ n m : ℕ, s = {some (some n, m)}} ∪
      {s : Set S156 | ∃ m : ℕ, some (none, m) ∈ s ∧
        {n : ℕ | some (some n, m) ∉ s}.Finite} ∪
      {s : Set S156 | none ∈ s ∧
        {m : ℕ | ¬ (some (none, m) ∈ s ∧ {n : ℕ | some (some n, m) ∉ s}.Finite)}.Finite})

end S156
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S156 as a bundled `Space` (carrier + topology). -/
noncomputable def S156 : Space := ⟨PiBase.Spaces.S156.S156, inferInstance⟩

end PiBase.Formal
