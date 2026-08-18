module

public import Mathlib.Topology.Compactness.CompactlyCoherentSpace
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Separation.Hausdorff
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 142. k₃-space -/
class K3Space (X : Type u) [TopologicalSpace X] : Prop where
  isCoherentWith : IsCoherentWith {K : Set X | T2Space K ∧ IsCompact K}

end PiBase

namespace PiBase.Formal

def P142 : Property where
  toPred := K3Space
  well_defined φ h := by
    have hX_coh := h.isCoherentWith
    constructor
    refine ⟨fun t ht => ?_⟩
    have h_pre_open : IsOpen (φ ⁻¹' t) := by
      rw [hX_coh.isOpen_iff]
      intro s hs
      have h_s_image_compact : IsCompact (φ '' s) := hs.2.image φ.continuous
      have h_s_image_t2 : T2Space (φ '' s) := by
        have : T2Space s := hs.1
        have e : s ≃ₜ φ '' s := φ.image s
        exact e.t2Space
      have hY := ht (φ '' s) ⟨h_s_image_t2, h_s_image_compact⟩
      let e : s ≃ₜ φ '' s := φ.image s
      have h_eq : (Subtype.val ⁻¹' (φ ⁻¹' t) : Set s) =
          e ⁻¹' (Subtype.val ⁻¹' t : Set (φ '' s)) := by
        ext ⟨x, hx⟩
        rfl
      rw [h_eq]
      exact e.isOpen_preimage.mpr hY
    exact φ.isOpen_preimage.mp h_pre_open

end PiBase.Formal
