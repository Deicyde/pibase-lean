module

public import Mathlib.Topology.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Filter TopologicalSpace

universe u

namespace PiBase

/- 193. Shrinking -/
class ShrinkingSpace (X : Type u) [TopologicalSpace X] : Prop where
  closure_refinement :
    ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → ⋃ a, s a = univ →
      ∃ (t : α → Set X), (∀ a, IsOpen (t a)) ∧ ⋃ a, t a = univ ∧ ∀ a, closure (t a) ⊆ s a

end PiBase

namespace PiBase.Formal

def P193 : Property where
  toPred := ShrinkingSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h := by
    constructor
    intro α s hs_open hs_cover
    have hs_open_X : ∀ a, IsOpen (φ ⁻¹' (s a)) := fun a => (hs_open a).preimage φ.continuous
    have hs_cover_X : ⋃ a, φ ⁻¹' (s a) = univ := by
      ext x
      simp only [mem_iUnion, mem_preimage, mem_univ, iff_true]
      have : φ x ∈ ⋃ a, s a := by rw [hs_cover]; trivial
      obtain ⟨a, ha⟩ := mem_iUnion.mp this
      exact ⟨a, ha⟩
    obtain ⟨t, ht_open, ht_cover, ht_closure⟩ :=
      h.closure_refinement α (fun a => φ ⁻¹' (s a)) hs_open_X hs_cover_X
    refine ⟨fun a => φ '' (t a), ?_, ?_, ?_⟩
    · intro a
      exact φ.isOpenMap _ (ht_open a)
    · ext y
      simp only [mem_iUnion, mem_image, mem_univ, iff_true]
      have : φ.symm y ∈ ⋃ a, t a := by rw [ht_cover]; trivial
      obtain ⟨a, ha⟩ := mem_iUnion.mp this
      exact ⟨a, φ.symm y, ha, by simp⟩
    · intro a
      calc closure (φ '' (t a)) = φ '' closure (t a) := (φ.image_closure (t a)).symm
        _ ⊆ φ '' (φ ⁻¹' (s a)) := by exact Set.image_mono (ht_closure a)
        _ ⊆ s a := by exact image_preimage_subset _ _

end PiBase.Formal
