module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Sum.Order
public import Mathlib.Topology.Order.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.SetTheory.Ordinal.Arithmetic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Ordinal Sum

namespace PiBase.Spaces
namespace S149

/- Space 149: Two-sided long line.
See https://topology.pi-base.org/spaces/S000149.
Built from the Long ray (S38) L = ω₁ ×ₗ [0,1): let L* be a reversed copy of L. As an
ordered set, X is L* followed by L with max(L*) and min(L) identified; it carries the
corresponding order topology. -/

/-- The Long ray (pi-Base S38): the lexicographic order topology on
`{o : Ordinal // o < ω₁} ×ₗ [0,1)`. Restated here (self-contained; this file must not
depend on `PiBaseLean.Spaces.S38`). -/
def LongRay149 : Type 1 := { o : Ordinal.{0} // o < ω₁ } ×ₗ ↥(Set.Ico (0 : ℝ) 1)

noncomputable instance : LinearOrder LongRay149 :=
  inferInstanceAs (LinearOrder ({o : Ordinal.{0} // o < ω₁} ×ₗ ↥(Set.Ico (0 : ℝ) 1)))

/-- `0 < ω₁`, needed to exhibit the minimum `(0, 0)` of the Long ray. -/
theorem zero_lt_omega_one : (0 : Ordinal.{0}) < ω₁ :=
  omega0_pos.trans omega0_lt_omega_one

/-- `(0, 0)`, the minimum element of the Long ray `L`. -/
def longRay149Bot : LongRay149 :=
  toLex (⟨0, zero_lt_omega_one⟩, ⟨0, le_refl 0, zero_lt_one⟩)

/-- The Two-sided long line (pi-Base S149) as an ordered set: the reversed Long ray `L*`
followed by the Long ray `L`, with `max(L*)` (the image of `min(L)` under order-reversal)
and `min(L)` identified. Concretely, this is the lexicographic sum `L*ᵒᵈ ⊕ₗ L` with the
duplicate copy of the gluing point (`inr (min L)`) removed, so `inl (⊤ : L*ᵒᵈ)` alone plays
the role of the shared point. -/
def S149 : Type 1 := { x : LongRay149ᵒᵈ ⊕ₗ LongRay149 // ofLex x ≠ Sum.inr longRay149Bot }

noncomputable instance : LinearOrder S149 :=
  inferInstanceAs (LinearOrder { x : LongRay149ᵒᵈ ⊕ₗ LongRay149 // ofLex x ≠ Sum.inr longRay149Bot })

noncomputable instance S149_top : TopologicalSpace S149 := Preorder.topology S149

instance : OrderTopology S149 := ⟨rfl⟩

end S149
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S149 as a bundled `Space` (carrier + topology). -/
noncomputable def S149 : Space := ⟨PiBase.Spaces.S149.S149, PiBase.Spaces.S149.S149_top⟩

end PiBase.Formal
