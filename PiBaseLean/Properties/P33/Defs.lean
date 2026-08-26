module

public import PiBaseLean.AdditionalDefs.Cover
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

universe u

open Topology Set Function Filter TopologicalSpace

namespace PiBase

/- 33. Countably metacompact -/
class CountablyMetacompactSpace (X : Type u) [TopologicalSpace X] : Prop where
  countably_metacompact :
    ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → (⋃ a, s a = univ) → Countable α →
      ∃ (β : Type u) (t : β → Set X),
        (∀ b, IsOpen (t b)) ∧ (⋃ b, t b = univ) ∧ PointFinite t ∧ ∀ b, ∃ a, t b ⊆ s a

end PiBase

namespace PiBase.Formal

def P33 : Property where
  toPred := CountablyMetacompactSpace
  well_defined := fun {X Y} _ _ φ h => by
    constructor
    intro α s hOpen hCover hCount
    let sX : α → Set X := fun a => φ ⁻¹' s a
    have hOpenX : ∀ a, IsOpen (sX a) := fun a => (hOpen a).preimage φ.continuous
    have hCoverX : (⋃ a, sX a = univ) := by
      have : (⋃ a, sX a) = φ ⁻¹' (⋃ a, s a) := by rw [Set.preimage_iUnion]
      rw [this, hCover, Set.preimage_univ]
    obtain ⟨β, t, htOpen, htCover, htPtFin, htRefine⟩ :=
      h.countably_metacompact α sX hOpenX hCoverX hCount
    refine ⟨β, fun b => φ '' t b, ?_, ?_, ?_, ?_⟩
    · intro b; exact φ.isOpen_image.mpr (htOpen b)
    · calc (⋃ b, φ '' t b : Set Y) = φ '' (⋃ b, t b) := by rw [Set.image_iUnion]
        _ = φ '' univ := by rw [htCover]
        _ = univ := Set.image_univ_of_surjective φ.surjective
    · intro y
      have heq : {b | y ∈ φ '' t b} = {b | φ.symm y ∈ t b} := by
        ext b
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨x, hx_mem, hx_eq⟩
          have : x = φ.symm y := φ.injective (by rw [hx_eq, φ.apply_symm_apply y])
          rw [this] at hx_mem; exact hx_mem
        · intro hy; exact ⟨φ.symm y, hy, φ.apply_symm_apply y⟩
      rw [heq]; exact htPtFin (φ.symm y)
    · intro b
      obtain ⟨a, ha⟩ := htRefine b
      refine ⟨a, ?_⟩
      intro y hy
      obtain ⟨x, hxt, rfl⟩ := hy
      exact ha hxt

end PiBase.Formal
