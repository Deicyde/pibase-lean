module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Data.Prod.Lex
public import Mathlib.Topology.Order.Basic
public import Mathlib.Data.Real.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S153

/- Space 153: Open long ray.
See https://topology.pi-base.org/spaces/S000153.
Let `Y = {o : Ordinal // o < ω₁} ×ₗ [0,1)` carry the lexicographic order topology (the
closed long ray, {S38}). The open long ray is `Y` with its first element `⟨0,0⟩` removed,
carrying the subspace topology (equivalently the order topology, since the result is
order-convex in `Y`). -/

/-- The closed long ray {S38}: the lexicographic order on
`{o : Ordinal // o < ω₁} ×ₗ [0,1)`, matching `PiBaseLean.Spaces.S38`. -/
abbrev S153.Y : Type 1 := { o : Ordinal.{0} // o < ω₁ } ×ₗ ↥(Set.Ico (0 : ℝ) 1)

/-- The first point of `Y`: the pair `⟨0, 0⟩` under the lexicographic order. -/
noncomputable def S153.zero : S153.Y :=
  toLex (⟨0, Ordinal.omega_pos 1⟩, ⟨0, Set.left_mem_Ico.mpr zero_lt_one⟩)

/-- Open long ray (pi-Base S153): the closed long ray `Y` (pi-Base {S38}) with its first
point `⟨0,0⟩` removed, carrying the subspace topology. -/
def S153 : Type 1 := {p : S153.Y // p ≠ S153.zero}

noncomputable instance : LinearOrder S153.Y :=
  inferInstanceAs (LinearOrder ({o : Ordinal.{0} // o < ω₁} ×ₗ ↥(Set.Ico (0 : ℝ) 1)))

noncomputable instance : TopologicalSpace S153.Y := Preorder.topology S153.Y

instance S153_top : TopologicalSpace S153 :=
  inferInstanceAs (TopologicalSpace {p : S153.Y // p ≠ S153.zero})

end S153
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S153 as a bundled `Space` (carrier + topology). -/
noncomputable def S153 : Space := ⟨PiBase.Spaces.S153.S153, PiBase.Spaces.S153.S153_top⟩

end PiBase.Formal
