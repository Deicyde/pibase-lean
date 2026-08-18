module

public import PiBaseLean.AdditionalDefs.Cover
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 88. Collectionwise normal -/
class CollectionwiseNormalSpace (X : Type u) [TopologicalSpace X] : Prop where
  collectionwise_normal : ∀ {ι : Type u} (F : ι → Set X),
      IsDiscreteFamily F → (∀ i : ι, IsClosed (F i)) →
        ∃ U : ι → Set X, (univ.PairwiseDisjoint U) ∧
          (∀ i : ι, IsOpen (U i)) ∧ (∀ i : ι, F i ⊆ U i)

end PiBase

namespace PiBase.Formal

def P88 : Property where
  toPred := CollectionwiseNormalSpace
  well_defined φ h := by
    constructor
    intro ι F hDisc hClosed
    have hDiscX : IsDiscreteFamily (fun i => φ ⁻¹' (F i)) := by
      intro x
      obtain ⟨V, hV_mem, hV_sub⟩ := hDisc (φ x)
      refine ⟨φ ⁻¹' V, φ.continuous.continuousAt.preimage_mem_nhds hV_mem, ?_⟩
      intro a ha b hb
      have ha' : (F a ∩ V).Nonempty := by
        obtain ⟨z, hz⟩ := ha
        rw [mem_inter_iff, mem_preimage, mem_preimage] at hz
        exact ⟨φ z, hz⟩
      have hb' : (F b ∩ V).Nonempty := by
        obtain ⟨z, hz⟩ := hb
        rw [mem_inter_iff, mem_preimage, mem_preimage] at hz
        exact ⟨φ z, hz⟩
      exact hV_sub ha' hb'
    have hClosedX : ∀ i, IsClosed (φ ⁻¹' (F i)) := fun i =>
      (hClosed i).preimage φ.continuous
    obtain ⟨U, hDisj, hOpen, hSub⟩ := h.collectionwise_normal _ hDiscX hClosedX
    refine ⟨fun i => φ '' (U i), ?_, fun i => φ.isOpenMap _ (hOpen i), ?_⟩
    · intro a _ b _ hab
      have hDisj_ab : Disjoint (U a) (U b) := hDisj (mem_univ a) (mem_univ b) hab
      change Disjoint (φ '' U a) (φ '' U b)
      rw [Set.disjoint_left] at hDisj_ab ⊢
      rintro y ⟨x1, hx1U, hx1eq⟩ ⟨x2, hx2U, hx2eq⟩
      have hx : x1 = x2 := φ.injective (hx1eq.trans hx2eq.symm)
      exact hDisj_ab hx1U (hx ▸ hx2U)
    · intro i y hy
      have h_mem_pre : φ.symm y ∈ φ ⁻¹' (F i) := by
        rw [mem_preimage]
        simp [hy]
      have h_mem_U : φ.symm y ∈ U i := hSub i h_mem_pre
      exact ⟨φ.symm y, h_mem_U, φ.apply_symm_apply y⟩

end PiBase.Formal
