module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Real.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S93

/- Space 93: Double arrow space (split interval).
See https://topology.pi-base.org/spaces/S000093.
The set X = ([0,1] × {0,1}) \ {⟨0,0⟩, ⟨1,1⟩}, ordered lexicographically
(⟨x,t⟩ < ⟨x',t'⟩ ↔ x < x' ∨ (x = x' ∧ t < t')), carrying the order topology. -/

/-- The double arrow space / split interval (pi-Base S93): the lexicographically
ordered set `([0,1] × {0,1}) \ {⟨0,0⟩, ⟨1,1⟩}`, with `false`/`true` standing in for
the two copies `0`/`1` of the interval. -/
def S93 : Type :=
  { p : (Set.Icc (0 : ℝ) 1) ×ₗ Bool //
      p ≠ toLex (⟨0, le_refl 0, zero_le_one⟩, false) ∧
      p ≠ toLex (⟨1, zero_le_one, le_refl 1⟩, true) }

noncomputable instance : LinearOrder S93 := Subtype.instLinearOrder _

noncomputable instance : TopologicalSpace S93 := Preorder.topology S93

end S93
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S93 as a bundled `Space` (carrier + topology). -/
noncomputable def S93 : Space := ⟨PiBase.Spaces.S93.S93, inferInstance⟩

end PiBase.Formal
