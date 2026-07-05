module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces

/- Space 23: Arens-Fort Space.
See https://topology.pi-base.org/spaces/S000023.
Carrier `ℕ × ℕ`; every point other than `(0, 0)` is isolated, and a set
containing `(0, 0)` is open iff it contains all but finitely many points in
all but finitely many columns (a column being `{p | p.1 = n}` for some `n`). -/

/-- Arens-Fort space (pi-Base S23): the carrier is `ℕ × ℕ` (thought of as
`ω × ω`). -/
def S23 : Type := ℕ × ℕ

/-- The generating open sets: every singleton not containing `(0, 0)`, together
with every set containing `(0, 0)` that meets all but finitely many columns
`{p | p.1 = n}` in a cofinite subset of that column. -/
instance : TopologicalSpace S23 :=
  TopologicalSpace.generateFrom
    ({s : Set (ℕ × ℕ) | ∃ p : ℕ × ℕ, p ≠ (0, 0) ∧ s = {p}} ∪
      {s : Set (ℕ × ℕ) | (0, 0) ∈ s ∧
        {n : ℕ | ¬ Set.Finite {m : ℕ | (n, m) ∉ s}}.Finite})

end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S23 as a bundled `Space` (carrier + topology). -/
noncomputable def S23 : Space := ⟨PiBase.Spaces.S23, inferInstance⟩

end PiBase.Formal
