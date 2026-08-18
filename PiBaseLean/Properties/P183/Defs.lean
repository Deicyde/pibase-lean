module

public import PiBaseLean.AdditionalDefs.Cover
public import PiBaseLean.Properties.Bundled.Defs
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 183. Has a countable k-network -/
class HasCountableKNetwork (X : Type u) [TopologicalSpace X] : Prop where
  ex_network : ∃ (ι : Type) (f : ι → Set X), Countable ι ∧ IsKNetwork f

end PiBase

namespace PiBase.Formal

def P183 : Property where
  toPred := HasCountableKNetwork
  well_defined φ h := by
    rcases h with ⟨ι, f, hι_cnt, hf⟩
    refine ⟨ι, fun i => φ '' f i, hι_cnt, ?_⟩
    intro U K hUo hKc hKU
    have hU' : IsOpen (φ ⁻¹' U) := φ.isOpen_preimage.mpr hUo
    have hK'_eq : φ ⁻¹' K = φ.symm '' K := by
      ext x
      constructor
      · intro hx
        exact ⟨φ x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simp [hy]
    have hK' : IsCompact (φ ⁻¹' K) := by
      rw [hK'_eq]
      exact hKc.image φ.symm.continuous
    have hKU' : φ ⁻¹' K ⊆ φ ⁻¹' U := preimage_mono hKU
    obtain ⟨s, hK's, hUs⟩ := hf (φ ⁻¹' U) (φ ⁻¹' K) hU' hK' hKU'
    refine ⟨s, ?_, ?_⟩
    · -- K ⊆ ⋃ i ∈ s, φ '' f i
      intro y hyK
      have hy' : y ∈ φ '' (φ ⁻¹' K) := by
        rw [φ.image_preimage]
        exact hyK
      rcases hy' with ⟨x, hxK, rfl⟩
      have hxU : x ∈ ⋃ i ∈ s, f i := hK's hxK
      rcases Set.mem_iUnion₂.mp hxU with ⟨i, hi, hxi⟩
      exact Set.mem_iUnion₂.mpr ⟨i, hi, ⟨x, hxi, rfl⟩⟩
    · -- ⋃ i ∈ s, φ '' f i ⊆ U
      intro y hy
      rcases Set.mem_iUnion₂.mp hy with ⟨i, hi, hx⟩
      rcases hx with ⟨x, hxf, rfl⟩
      have : x ∈ ⋃ i ∈ s, f i := Set.mem_iUnion₂.mpr ⟨i, hi, hxf⟩
      have : x ∈ φ ⁻¹' U := hUs this
      exact this

end PiBase.Formal
