module

public import PiBaseLean.AdditionalDefs.Cardinal
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Filter TopologicalSpace

universe u

namespace PiBase

/- 173. Pseudoradial -/
class PseudoradialSpace (X : Type u) [TopologicalSpace X] : Prop where
  radiallyClosed_isClosed : ∀ ⦃s : Set X⦄, IsRadiallyClosed s → IsClosed s

end PiBase

namespace PiBase.Formal

def P173 : Property where
  toPred := PseudoradialSpace
  well_defined φ h := by
    constructor
    intro s hs
    have h_pre_radially : IsRadiallyClosed (φ ⁻¹' s) := by
      intro x hx
      obtain ⟨o, f, ho_pos, hf_range, hf_tend⟩ := hx
      have hf_range_Y : range (fun i => φ (f i)) ⊆ s := by
        intro y hy
        obtain ⟨i, rfl⟩ := hy
        have : f i ∈ φ ⁻¹' s := hf_range (mem_range_self i)
        simpa using this
      have hf_tend_Y : Tendsto (fun i => φ (f i)) atTop (𝓝 (φ x)) :=
        (φ.continuous.continuousAt).tendsto.comp hf_tend
      have : φ x ∈ s := hs (φ x) ⟨o, fun i => φ (f i), ho_pos, hf_range_Y, hf_tend_Y⟩
      exact this
    have h_pre_closed : IsClosed (φ ⁻¹' s) := h.radiallyClosed_isClosed h_pre_radially
    -- `s = φ.symm ⁻¹' (φ ⁻¹' s)`, so closedness transports by continuity of `φ.symm`.
    have h_symm_pre : IsClosed (φ.symm ⁻¹' (φ ⁻¹' s)) :=
      h_pre_closed.preimage φ.symm.continuous
    simpa [Set.preimage_preimage] using h_symm_pre

end PiBase.Formal
