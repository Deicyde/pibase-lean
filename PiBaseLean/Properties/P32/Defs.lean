module

public import Mathlib.Topology.LocallyFinite
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

universe u

open Topology Set Function Filter TopologicalSpace

namespace PiBase

/- 32. Countably paracompact -/
class CountablyParacompactSpace (X : Type u) [TopologicalSpace X] : Prop where
  countably_paracompact :
    ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → (⋃ a, s a = univ) → Countable α →
      ∃ (β : Type u) (t : β → Set X),
        (∀ b, IsOpen (t b)) ∧ (⋃ b, t b = univ) ∧ LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a

end PiBase

namespace PiBase.Formal

def P32 : Property where
  toPred := CountablyParacompactSpace
  well_defined := fun {X Y} _ _ φ h => by
    constructor
    intro α s hOpen hCover hCount
    let sX : α → Set X := fun a => φ ⁻¹' s a
    have hOpenX : ∀ a, IsOpen (sX a) := fun a => (hOpen a).preimage φ.continuous
    have hCoverX : (⋃ a, sX a = univ) := by
      have : (⋃ a, sX a) = φ ⁻¹' (⋃ a, s a) := by rw [Set.preimage_iUnion]
      rw [this, hCover, Set.preimage_univ]
    obtain ⟨β, t, htOpen, htCover, htLocFin, htRefine⟩ :=
      h.countably_paracompact α sX hOpenX hCoverX hCount
    refine ⟨β, fun b => φ '' t b, ?_, ?_, ?_, ?_⟩
    · intro b; exact φ.isOpen_image.mpr (htOpen b)
    · calc (⋃ b, φ '' t b : Set Y) = φ '' (⋃ b, t b) := by rw [Set.image_iUnion]
        _ = φ '' univ := by rw [htCover]
        _ = univ := Set.image_univ_of_surjective φ.surjective
    · intro y
      obtain ⟨u, hu_mem, hu_fin⟩ := htLocFin (φ.symm y)
      have hu_nhds_y : φ '' u ∈ 𝓝 y := by
        have h_eq : y = φ (φ.symm y) := (φ.apply_symm_apply y).symm
        rw [h_eq, ← φ.map_nhds_eq (φ.symm y), Filter.mem_map, φ.preimage_image]
        exact hu_mem
      refine ⟨φ '' u, hu_nhds_y, ?_⟩
      have heq : {b | (φ '' t b ∩ φ '' u).Nonempty} = {b | (t b ∩ u).Nonempty} := by
        ext b
        simp only [Set.mem_ofPred_eq, Set.Nonempty]
        constructor
        · rintro ⟨z, ⟨x1, hx1t, hx1eq⟩, ⟨x2, hx2u, hx2eq⟩⟩
          have hx_eq : x1 = x2 := φ.injective (hx1eq.trans hx2eq.symm)
          exact ⟨x1, hx1t, hx_eq ▸ hx2u⟩
        · rintro ⟨x, hxt, hxu⟩
          exact ⟨φ x, ⟨x, hxt, rfl⟩, ⟨x, hxu, rfl⟩⟩
      rw [heq]; exact hu_fin
    · intro b
      obtain ⟨a, ha⟩ := htRefine b
      refine ⟨a, ?_⟩
      intro y hy
      obtain ⟨x, hxt, rfl⟩ := hy
      exact ha hxt

end PiBase.Formal
