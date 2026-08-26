module

public import Mathlib.Topology.Defs.Filter
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 174. Well-based -/
class WellBasedSpace (X : Type u) [TopologicalSpace X] : Prop where
  basis_ordered : ∀ x : X, ∃ (ι : Type u) (s : ι → Set X), (∀ i : ι, x ∈ s i) ∧
    HasBasis (𝓝 x) (fun _ ↦ True) s ∧ ∀ (i j : ι), s i ⊆ s j ∨ s j ⊆ s i

end PiBase

namespace PiBase.Formal

def P174 : Property where
  toPred := WellBasedSpace
  well_defined φ h := by
    refine ⟨fun y => ?_⟩
    obtain ⟨ι, s, hs_mem, hs_basis, hs_ord⟩ := h.basis_ordered (φ.symm y)
    refine ⟨ι, fun i => φ '' (s i), fun i => ⟨φ.symm y, hs_mem i, by simp⟩, ?_, ?_⟩
    · have hmap : Filter.map φ (𝓝 (φ.symm y)) = 𝓝 y := by
        rw [φ.map_nhds_eq, Homeomorph.apply_symm_apply]
      rw [← hmap]
      exact hs_basis.map φ
    · intro i j
      rcases hs_ord i j with hij | hij
      · exact Or.inl (Set.image_mono hij)
      · exact Or.inr (Set.image_mono hij)

end PiBase.Formal
