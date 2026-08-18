module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Defs.Filter
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Set

namespace PiBase

/- 136. Anticompact -/
class AnticompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  compact_finite (s : Set X) : IsCompact s → s.Finite

end PiBase

namespace PiBase.Formal

def P136 : Property where
  toPred := AnticompactSpace
  well_defined φ h := by
    constructor
    intro s hs
    -- map compact s:Y through φ.symm to get compact preimage in X
    have h_eq : φ ⁻¹' s = φ.symm '' s := by
      ext x
      constructor
      · intro hx
        exact ⟨φ x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simp [hy]
    have hs' : IsCompact (φ ⁻¹' s) := by
      rw [h_eq]
      exact φ.symm.isCompact_image.mpr hs
    have hf := h.compact_finite _ hs'
    have h_pre : s = φ '' (φ ⁻¹' s) := (φ.image_preimage s).symm
    rw [h_pre]
    exact hf.image _

end PiBase.Formal
