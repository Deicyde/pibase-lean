module

public import Mathlib.Topology.Separation.Hausdorff
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Filter TopologicalSpace

universe u

namespace PiBase

/- 171. k₂-Hausdorff -/
class K2T2Space (X : Type u) [TopologicalSpace X] : Prop where
  closed_continuous : ∀ ⦃K : Type u⦄ {_ : TopologicalSpace K} (f : K → X × X),
    T2Space K → CompactSpace K → Continuous f → IsClosed (f ⁻¹' (diagonal X))

end PiBase

namespace PiBase.Formal

def P171 : Property where
  toPred := K2T2Space
  well_defined := fun {X Y} _ _ φ h => by
    refine ⟨fun K _ f hT2 hComp hCont => ?_⟩
    -- Transport along `φ.symm` componentwise: `f k` is diagonal in `Y` iff its
    -- image under `Prod.map φ.symm φ.symm` is diagonal in `X`, since `φ.symm` is injective.
    have hg : Continuous (Prod.map φ.symm φ.symm ∘ f) :=
      (φ.symm.continuous.prodMap φ.symm.continuous).comp hCont
    have hclosed := h.closed_continuous (Prod.map φ.symm φ.symm ∘ f) hT2 hComp hg
    have h_eq : (Prod.map φ.symm φ.symm ∘ f) ⁻¹' (diagonal X) = f ⁻¹' (diagonal Y) := by
      ext k
      constructor
      · intro hk
        have hk' : φ.symm (f k).1 = φ.symm (f k).2 := hk
        exact φ.symm.injective hk'
      · intro hk
        have hk' : (f k).1 = (f k).2 := hk
        change φ.symm (f k).1 = φ.symm (f k).2
        rw [hk']
    exact h_eq ▸ hclosed

end PiBase.Formal
