module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Defs.Filter
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set

universe u

namespace PiBase

/- 111. Hemicompact -/
class HemicompactSpace (X : Type u) [TopologicalSpace X] : Prop where
  hemicompact : ∃ (ι : Type u) (K : ι → Set X), Countable ι ∧
    (∀ i, IsCompact (K i)) ∧ ⋃ i, K i = univ ∧ ∀ t : Set X, IsCompact t → ∃ i : ι, t ⊆ K i

end PiBase

namespace PiBase.Formal

def P111 : Property where
  toPred := HemicompactSpace
  well_defined φ h := by
    obtain ⟨ι, K, hCount, hComp, hUniv, hCof⟩ := h.hemicompact
    refine ⟨⟨ι, fun i => φ '' K i, hCount, ?_, ?_, ?_⟩⟩
    · exact fun i => IsCompact.image (hComp i) φ.continuous
    · rw [← image_iUnion, hUniv, image_univ, EquivLike.range_eq_univ]
    · intro t ht
      have ht' : IsCompact (φ.symm '' t) := IsCompact.image ht φ.symm.continuous
      obtain ⟨i, hi⟩ := hCof _ ht'
      refine ⟨i, fun y hy => ?_⟩
      exact ⟨φ.symm y, hi ⟨y, hy, rfl⟩, φ.apply_symm_apply y⟩

end PiBase.Formal
