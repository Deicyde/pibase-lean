module

public import Mathlib.Order.Filter.Bases.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Lemmas
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Function Set Filter Topology TopologicalSpace

namespace PiBase

/- 24. Locally relatively compact -/
class LocallyRelativelyCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  locally_relatively_compact : ∀ x : X, (𝓝 x).HasBasis (fun s => s ∈ 𝓝 x ∧ IsCompact (closure s)) id

end PiBase

namespace PiBase.Formal

def P24 : Property where
  toPred := LocallyRelativelyCompactSpace
  well_defined φ h := by
    constructor
    intro y
    let x := φ.symm y
    have hX := h.locally_relatively_compact x
    have h_eq : Filter.map φ (𝓝 x) = 𝓝 y := by
      have hmap := φ.map_nhds_eq x
      have hxy : φ x = y := φ.apply_symm_apply y
      calc Filter.map φ (𝓝 x) = 𝓝 (φ x) := hmap
        _ = 𝓝 y := by rw [hxy]
    have h_basis : (𝓝 y).HasBasis (fun s => s ∈ 𝓝 x ∧ IsCompact (closure s)) (fun s => φ '' s) := by
      rw [← h_eq]
      exact hX.map φ
    have h_target : (𝓝 y).HasBasis (fun t => t ∈ 𝓝 y ∧ IsCompact (closure t)) id := by
      apply h_basis.to_hasBasis'
      · intro s hs
        refine ⟨φ '' s, ?_, Subset.rfl⟩
        constructor
        · exact h_basis.mem_of_mem hs
        · have h_compact : IsCompact (closure s) := hs.2
          have h_img_compact : IsCompact (φ '' closure s) := h_compact.image φ.continuous
          have h_closure_eq : φ '' closure s = closure (φ '' s) := φ.image_closure s
          have : IsCompact (closure (φ '' s)) := by
            rw [← h_closure_eq]
            exact h_img_compact
          exact this
      · intro t ht
        exact ht.1
    exact h_target

end PiBase.Formal
