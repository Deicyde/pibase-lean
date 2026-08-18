module

public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

universe u

open Cardinal Set

namespace PiBase

/-- 219. Toronto -/
class TorontoSpace (X : Type*) [TopologicalSpace X] : Prop where
  toronto : ∀ ⦃Y : Set X⦄, #Y = #X → Nonempty (Y ≃ₜ X)

end PiBase

namespace PiBase.Formal

def P219 : Property where
  toPred := TorontoSpace
  well_defined {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z] (φ : X ≃ₜ Z) h := by
    constructor
    intro Y hcard
    -- Pull `Y` back along `φ`; the preimage is homeomorphic to `Y` and has the same cardinality.
    have himg : φ '' (φ ⁻¹' Y) = Y := image_preimage_eq Y φ.surjective
    let e : (φ ⁻¹' Y : Set X) ≃ₜ (Y : Set Z) :=
      (φ.image (φ ⁻¹' Y)).trans (Homeomorph.setCongr himg)
    have hcardX : #(φ ⁻¹' Y : Set X) = #X :=
      (Cardinal.mk_congr e.toEquiv).trans (hcard.trans (Cardinal.mk_congr φ.toEquiv).symm)
    obtain ⟨eX⟩ := h.toronto hcardX
    exact ⟨e.symm.trans (eX.trans φ)⟩

end PiBase.Formal
