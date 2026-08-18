module

public import Mathlib.Topology.Separation.Hausdorff
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 143. Weak Hausdorff -/
class WeakT2Space (X : Type u) [TopologicalSpace X] : Prop where
  compact_closed : ∀ {K : Type u} (_ : TopologicalSpace K) ⦃f : K → X⦄,
    Continuous f → CompactSpace K → T2Space K → IsClosed (range f)

end PiBase

namespace PiBase.Formal

def P143 : Property where
  toPred := WeakT2Space
  well_defined φ h := by
    constructor
    intro K tK f hfCont hComp hT2
    have h_eq : φ ⁻¹' (range f) = range (φ.symm ∘ f) := by
      ext x
      simp only [mem_preimage, mem_range, comp_apply]
      constructor
      · rintro ⟨y, hy⟩
        -- hy : f y = φ x, need φ.symm (f y) = x
        refine ⟨y, ?_⟩
        calc φ.symm (f y) = φ.symm (φ x) := by rw [hy]
        _ = x := φ.symm_apply_apply x
      · rintro ⟨y, hy⟩
        -- hy : φ.symm (f y) = x, need f y = φ x
        have : f y = φ x := by
          calc f y = φ (φ.symm (f y)) := (φ.apply_symm_apply (f y)).symm
          _ = φ x := by rw [hy]
        exact ⟨y, this⟩
    rw [← φ.isClosed_preimage]
    rw [h_eq]
    exact h.compact_closed tK (φ.symm.continuous.comp hfCont) hComp hT2

end PiBase.Formal
