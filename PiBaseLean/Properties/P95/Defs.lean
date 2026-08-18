module

public import Mathlib.Topology.Path
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function

namespace PiBase

/- 95. Arc connected -/
class ArcConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  joined : Pairwise fun x y : X ↦ ∃ f : Path x y, IsEmbedding f

end PiBase

namespace PiBase.Formal

open PiBase

def P95 : Property where
  toPred := ArcConnectedSpace
  well_defined φ h := by
    constructor
    intro x y hxy
    have hxy' : φ.symm x ≠ φ.symm y := by
      intro heq
      apply hxy
      calc x = φ (φ.symm x) := (φ.apply_symm_apply x).symm
        _ = φ (φ.symm y) := by rw [heq]
        _ = y := φ.apply_symm_apply y
    obtain ⟨p, hp⟩ := h.joined hxy'
    have h_comp : IsEmbedding (φ ∘ ⇑p) := φ.isEmbedding.comp hp
    have h_map_eq : (⇑(p.map φ.continuous) : unitInterval → _) = φ ∘ ⇑p := by
      ext t
      rfl
    have h_map : IsEmbedding (p.map φ.continuous) := by
      rw [h_map_eq]
      exact h_comp
    let q := (p.map φ.continuous).cast (show x = φ (φ.symm x) from (φ.apply_symm_apply x).symm)
      (show y = φ (φ.symm y) from (φ.apply_symm_apply y).symm)
    have h_q : IsEmbedding q := by
      have heq : (⇑q : unitInterval → _) = ⇑(p.map φ.continuous) := by
        simp only [q, Path.cast_coe]
      rw [heq]
      exact h_map
    exact ⟨q, h_q⟩

end PiBase.Formal
