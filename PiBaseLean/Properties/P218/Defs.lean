module

public import Mathlib.Topology.Defs.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

universe u

namespace PiBase

/- 218. Ultranormal -/
class UltranormalSpace (X : Type*) [TopologicalSpace X] : Prop where
  disjoint_clopen {s t : Set X} (st : Disjoint s t) (hs : IsClosed s) (ht : IsClosed t) :
    ∃ r : Set X, IsClopen r ∧ s ⊆ r ∧ t ⊆ rᶜ

end PiBase

namespace PiBase.Formal

def P218 : Property where
  toPred := UltranormalSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h := by
    constructor
    intro s t hdisj hs ht
    have hsX : IsClosed (φ ⁻¹' s) := φ.isClosed_preimage.mpr hs
    have htX : IsClosed (φ ⁻¹' t) := φ.isClosed_preimage.mpr ht
    have hdisjX : Disjoint (φ ⁻¹' s) (φ ⁻¹' t) := hdisj.preimage φ
    obtain ⟨rX, hrXc, hrXsub, htXsub⟩ := h.disjoint_clopen hdisjX hsX htX
    refine ⟨φ '' rX, ?_, ?_, ?_⟩
    · have hClosed : IsClosed (φ '' rX) := φ.isClosedMap rX hrXc.1
      have hOpen : IsOpen (φ '' rX) := φ.isOpenMap rX hrXc.2
      exact ⟨hClosed, hOpen⟩
    · calc s = φ '' (φ ⁻¹' s) := (φ.image_preimage s).symm
        _ ⊆ φ '' rX := Set.image_mono hrXsub
    · intro y hy
      rintro ⟨x, hx, rfl⟩
      exact htXsub hy hx

end PiBase.Formal
