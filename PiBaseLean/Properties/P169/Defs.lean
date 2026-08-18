module

public import PiBaseLean.AdditionalDefs.Constructions
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 169. Semi-hausdorff -/
class SemiT2Space (X : Type u) [TopologicalSpace X] : Prop where
  ex_regular_open : Pairwise fun x y ↦ ∃ s : Set X, IsRegularOpen s ∧ x ∈ s ∧ y ∉ s

end PiBase

namespace PiBase.Formal

def P169 : Property where
  toPred := SemiT2Space
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h := by
    refine ⟨fun y₁ y₂ hne => ?_⟩
    obtain ⟨s, hs_reg, hs_mem, hs_nmem⟩ :=
      h.ex_regular_open (φ.symm.injective.ne hne)
    refine ⟨φ '' s, ?_, ⟨φ.symm y₁, hs_mem, by simp⟩, ?_⟩
    · change interior (closure (φ '' s)) = φ '' s
      rw [← φ.image_closure, ← φ.image_interior, hs_reg]
    · rintro ⟨x, hx, rfl⟩
      exact hs_nmem (by simpa using hx)

end PiBase.Formal
