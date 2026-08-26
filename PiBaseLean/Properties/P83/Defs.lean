module

public import PiBaseLean.AdditionalDefs.Cover
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 83. Meta Lindelöf -/
class MetaLindelofSpace (X : Type u) [TopologicalSpace X] : Prop where
  meta_lindelof :
    ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → (⋃ a, s a = univ) →
      ∃ (β : Type u) (t : β → Set X),
        (∀ b, IsOpen (t b)) ∧ (⋃ b, t b = univ) ∧ PointCountable t ∧ ∀ b, ∃ a, t b ⊆ s a

end PiBase

namespace PiBase.Formal

def P83 : Property where
  toPred := MetaLindelofSpace
  well_defined := fun {X Y} _ _ φ h => by
    constructor
    intro α s hOpen hCover
    let sX : α → Set X := fun a => φ ⁻¹' s a
    have hOpenX : ∀ a, IsOpen (sX a) := fun a => (hOpen a).preimage φ.continuous
    have hCoverX : (⋃ a, sX a) = univ := by
      have : (⋃ a, sX a) = φ ⁻¹' (⋃ a, s a) := by rw [preimage_iUnion]
      rw [this, hCover, preimage_univ]
    obtain ⟨β, t, htOpen, htCover, htPtCount, htRefine⟩ := h.meta_lindelof α sX hOpenX hCoverX
    refine ⟨β, fun b => φ '' t b, ?_, ?_, ?_, ?_⟩
    · intro b; exact φ.isOpen_image.mpr (htOpen b)
    · calc (⋃ b, φ '' t b : Set Y) = φ '' (⋃ b, t b) := by rw [image_iUnion]
        _ = φ '' univ := by rw [htCover]
        _ = univ := image_univ_of_surjective φ.surjective
    · intro y
      have heq : {b | y ∈ φ '' t b} = {b | φ.symm y ∈ t b} := by
        ext b
        simp only [mem_ofPred_eq]
        constructor
        · rintro ⟨x, hx_mem, hx_eq⟩
          have : x = φ.symm y := φ.injective (by rw [hx_eq, φ.apply_symm_apply y])
          rw [this] at hx_mem; exact hx_mem
        · intro hy; exact ⟨φ.symm y, hy, φ.apply_symm_apply y⟩
      rw [heq]; exact htPtCount (φ.symm y)
    · intro b
      obtain ⟨a, ha⟩ := htRefine b
      refine ⟨a, ?_⟩
      intro y hy
      obtain ⟨x, hxt, rfl⟩ := hy
      exact ha hxt

end PiBase.Formal
