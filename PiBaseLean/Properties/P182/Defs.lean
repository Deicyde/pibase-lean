module

public import PiBaseLean.AdditionalDefs.Cover
public import Mathlib.Data.Set.Countable
public import Mathlib.Topology.Homeomorph.Defs
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

universe u

open Topology Set Function Filter TopologicalSpace

namespace PiBase

/- 182. Has a countable network -/ --NOTE: We use `Type` instead of `Type u` to be able to use `ℕ`
class HasCountableNetwork (X : Type u) [TopologicalSpace X] : Prop where
  has_countable_network : ∃ (ι : Type) (f : ι → Set X), Countable ι ∧ IsNetwork f

end PiBase

namespace PiBase.Formal

def P182 : Property where
  toPred := HasCountableNetwork
  well_defined φ h := by
    rcases h with ⟨ι, f, hι_cnt, hf⟩
    refine ⟨ι, fun i => φ '' f i, hι_cnt, ?_⟩
    intro y s hs
    have h_mem_comap : φ ⁻¹' s ∈ comap φ (𝓝 y) := by
      rw [Filter.mem_comap]
      exact ⟨s, hs, Subset.rfl⟩
    have h_comap_eq : comap φ (𝓝 y) = 𝓝 (φ.symm y) := φ.comap_nhds_eq y
    have h_pre : φ ⁻¹' s ∈ 𝓝 (φ.symm y) := h_comap_eq ▸ h_mem_comap
    obtain ⟨i, hi_mem, hi_sub⟩ := hf (φ.symm y) (φ ⁻¹' s) h_pre
    refine ⟨i, ?_, ?_⟩
    · exact ⟨φ.symm y, hi_mem, φ.apply_symm_apply y⟩
    · intro z hz
      rcases hz with ⟨w, hw_mem, rfl⟩
      have hw_in : w ∈ φ ⁻¹' s := hi_sub hw_mem
      exact hw_in

end PiBase.Formal
