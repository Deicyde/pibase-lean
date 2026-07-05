module

public import Mathlib.Topology.Constructions
public import PiBaseLean.Spaces.S39.Defs

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S196

/- Space 196: Long circle.
See https://topology.pi-base.org/spaces/S000196.
The quotient of the closed long ray (S39) identifying its least and greatest points,
carrying the quotient topology. -/

/-- The least ordinal component `⊥ : S39.Ord`, using that `S39.Ord` (ordinals `≤ ω₁`) is a
nonempty well-founded linear order and hence has a bottom element. -/
noncomputable instance : OrderBot S39.Ord :=
  WellFoundedLT.toOrderBot S39.Ord

/-- The least point of the closed long ray: `⟨⊥, 0⟩`, i.e. the bottom ordinal paired with
`0 ∈ [0,1)`. -/
noncomputable def S196.botPoint : S39.Ord ×ₗ S39.Unit :=
  toLex (⊥, (⟨0, by norm_num⟩ : S39.Unit))

/-- `S196.botPoint ≤ S39.topPoint`, so the least point of the closed long ray really is a
point of the subtype `S39 = {p // p ≤ S39.topPoint}`. -/
theorem S196.botPoint_le : S196.botPoint ≤ S39.topPoint :=
  Prod.Lex.toLex_le_toLex'.2 ⟨bot_le, fun _ => le_refl _⟩

/-- The least point of `S39`, as an element of the subtype `S39 = {p // p ≤ S39.topPoint}`. -/
noncomputable def S196.bot : S39 := ⟨S196.botPoint, S196.botPoint_le⟩

/-- The greatest point of `S39`, as an element of the subtype. -/
noncomputable def S196.top : S39 := ⟨S39.topPoint, le_refl _⟩

/-- The relation identifying only the least and greatest points of `S39` (and no others). -/
def S196.Rel (x y : S39) : Prop :=
  x = y ∨ (x = S196.bot ∧ y = S196.top) ∨ (x = S196.top ∧ y = S196.bot)

/-- `S196.Rel` is an equivalence relation: it only ever merges the two endpoints. -/
noncomputable def S196.setoid : Setoid S39 where
  r := S196.Rel
  iseqv := by
    refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
    · intro x y hxy
      rcases hxy with h | ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr ⟨hy, hx⟩)
      · exact Or.inr (Or.inl ⟨hy, hx⟩)
    · intro x y z hxy hyz
      rcases hxy with hxy | ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact hxy ▸ hyz
      · rcases hyz with hyz | ⟨hy', hz⟩ | ⟨hy', hz⟩
        · exact Or.inr (Or.inl ⟨hx, hyz.symm.trans hy⟩)
        · exact Or.inr (Or.inl ⟨hx, hz⟩)
        · exact Or.inl (hx.trans hz.symm)
      · rcases hyz with hyz | ⟨hy', hz⟩ | ⟨hy', hz⟩
        · exact Or.inr (Or.inr ⟨hx, hyz.symm.trans hy⟩)
        · exact Or.inl (hx.trans hz.symm)
        · exact Or.inr (Or.inr ⟨hx, hz⟩)

/-- Long circle (pi-Base S196): the closed long ray (S39) with its two endpoints
identified, carrying the quotient topology. -/
def S196 : Type := Quotient S196.setoid

noncomputable instance S196_top : TopologicalSpace S196 :=
  inferInstanceAs (TopologicalSpace (Quotient S196.setoid))

end S196
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S196 as a bundled `Space` (carrier + topology). -/
noncomputable def S196 : Space := ⟨PiBase.Spaces.S196.S196, PiBase.Spaces.S196.S196_top⟩

end PiBase.Formal
