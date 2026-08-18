module

public import PiBaseLean.AdditionalDefs.Cover
public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 54. Has a σ-locally finite basis -/
class HasSigmaLocallyFiniteBasis (X : Type u) [TopologicalSpace X] : Prop where
  ex_basis : ∃ (ι : Type u), ∃ (f : ι → Set X),
    Sigma LocallyFinite f ∧ (∀ (i : ι), IsOpen (f i)) ∧
      ∀ᵉ (x : X) (s ∈ 𝓝 x), ∃ (i : ι), x ∈ f i ∧ f i ⊆ s

end PiBase

namespace PiBase.Formal

def P54 : Property where
  toPred := HasSigmaLocallyFiniteBasis
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h := by
    obtain ⟨ι, f, ⟨ω, r, hω_count, hω_cover, hω_lf⟩, hf_open, hf_basis⟩ := h.ex_basis
    refine ⟨ι, fun i => φ '' f i, ?_, ?_, ?_⟩
    · refine ⟨ω, r, hω_count, hω_cover, ?_⟩
      intro w y
      obtain ⟨u, hu_mem, hu_fin⟩ := hω_lf w (φ.symm y)
      have hu_nhds : φ '' u ∈ 𝓝 y := by
        have hy : y = φ (φ.symm y) := (φ.apply_symm_apply y).symm
        rw [hy, ← φ.map_nhds_eq (φ.symm y), mem_map, φ.preimage_image]
        exact hu_mem
      refine ⟨φ '' u, hu_nhds, ?_⟩
      have heq : {j : r w | (φ '' f j.val ∩ φ '' u).Nonempty} =
          {j : r w | (f j.val ∩ u).Nonempty} := by
        ext j
        simp only [mem_ofPred_eq, Set.Nonempty, mem_inter_iff, mem_image]
        constructor
        · rintro ⟨z, ⟨x1, hx1, rfl⟩, x2, hx2, h_eq⟩
          exact ⟨x1, hx1, (φ.injective h_eq) ▸ hx2⟩
        · rintro ⟨x, hxf, hxu⟩
          exact ⟨φ x, ⟨x, hxf, rfl⟩, x, hxu, rfl⟩
      rw [heq]
      exact hu_fin
    · intro i
      exact φ.isOpenMap _ (hf_open i)
    · intro y s hs
      have hsX : φ ⁻¹' s ∈ 𝓝 (φ.symm y) := by
        rw [← φ.comap_nhds_eq y]
        exact mem_comap.mpr ⟨s, hs, Subset.rfl⟩
      obtain ⟨i, hfi_mem, hfi_sub⟩ := hf_basis (φ.symm y) (φ ⁻¹' s) hsX
      refine ⟨i, ⟨φ.symm y, hfi_mem, φ.apply_symm_apply y⟩, ?_⟩
      calc φ '' f i ⊆ φ '' (φ ⁻¹' s) := image_mono hfi_sub
        _ = s := φ.image_preimage s

end PiBase.Formal
