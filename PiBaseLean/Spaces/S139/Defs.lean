module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Constructions

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S139

/- Space 139: Countable bouquet of circles.
See https://topology.pi-base.org/spaces/S000139.
The quotient ℝ/ℤ obtained from the Euclidean line by collapsing all of ℤ to a single point. -/

/-- The equivalence relation on `ℝ` identifying two reals when they are equal, or when both
are integers (so all of `ℤ` is collapsed to a single point, everything else left alone). -/
def S139.r (x y : ℝ) : Prop := x = y ∨ ((∃ m : ℤ, x = m) ∧ (∃ n : ℤ, y = n))

theorem S139.r.equivalence : Equivalence S139.r where
  refl _ := Or.inl rfl
  symm h := h.elim (fun e => Or.inl e.symm) (fun ⟨hm, hn⟩ => Or.inr ⟨hn, hm⟩)
  trans hab hbc := by
    rcases hab with hab | ⟨hma, hnb⟩
    · rcases hbc with hbc | ⟨hmb, hnc⟩
      · exact Or.inl (hab.trans hbc)
      · exact Or.inr ⟨hab ▸ hmb, hnc⟩
    · rcases hbc with hbc | ⟨_, hnc⟩
      · exact Or.inr ⟨hma, hbc ▸ hnb⟩
      · exact Or.inr ⟨hma, hnc⟩

instance S139.setoid : Setoid ℝ := ⟨S139.r, S139.r.equivalence⟩

/-- Countable bouquet of circles (pi-Base S139): the quotient of `ℝ` (Euclidean topology)
by collapsing all of `ℤ` to a single point. -/
def S139 : Type := Quotient S139.setoid

instance S139_top : TopologicalSpace S139 := inferInstanceAs (TopologicalSpace (Quotient S139.setoid))

end S139
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S139 as a bundled `Space` (carrier + topology). -/
noncomputable def S139 : Space := ⟨PiBase.Spaces.S139.S139, PiBase.Spaces.S139.S139_top⟩

end PiBase.Formal
