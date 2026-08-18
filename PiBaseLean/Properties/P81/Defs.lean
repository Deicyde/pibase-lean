module

public import Mathlib.Data.Set.Countable
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function TopologicalSpace

namespace PiBase

/- 81. Countably tight -/
class CountablyTightSpace (X : Type*) [TopologicalSpace X] : Prop where
  countably_tight : ∀ (x : X) (A : Set X), x ∈ closure A → ∃ D : Set X,
    D.Countable ∧ D ⊆ A ∧ x ∈ closure D

end PiBase

namespace PiBase.Formal

def P81 : Property where
  toPred := CountablyTightSpace
  well_defined φ h := by
    constructor
    intro y A hy
    have h_mem_pre : φ.symm y ∈ φ ⁻¹' closure A := by
      rw [Set.mem_preimage, φ.apply_symm_apply]
      exact hy
    have h_eq : φ ⁻¹' closure A = closure (φ ⁻¹' A) := φ.preimage_closure A
    have h_mem : φ.symm y ∈ closure (φ ⁻¹' A) := h_eq ▸ h_mem_pre
    obtain ⟨D, hD_cnt, hD_sub, hD_cl⟩ := h.countably_tight (φ.symm y) (φ ⁻¹' A) h_mem
    refine ⟨φ '' D, hD_cnt.image _, ?_, ?_⟩
    · intro z hz
      rcases hz with ⟨x, hxD, rfl⟩
      have : x ∈ φ ⁻¹' A := hD_sub hxD
      rwa [Set.mem_preimage] at this
    · have h_img : φ '' closure D = closure (φ '' D) := φ.image_closure D
      have h_y : y ∈ φ '' closure D := ⟨φ.symm y, hD_cl, φ.apply_symm_apply y⟩
      rwa [h_img] at h_y

end PiBase.Formal
