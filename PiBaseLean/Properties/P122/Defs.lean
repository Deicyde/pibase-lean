module

public import PiBaseLean.Properties.Bundled.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 122. Locally Euclidean -/
class LocallyEuclideanSpace (X : Type u) [TopologicalSpace X] : Prop where
  locally_homeomorph (x : X) : ∃ n : ℕ, ∃ s ∈ 𝓝 x, Nonempty (s ≃ₜ (Fin n → ℝ))

end PiBase

namespace PiBase.Formal

def P122 : Property where
  toPred := LocallyEuclideanSpace
  well_defined φ h := by
    refine @LocallyEuclideanSpace.mk _ _ fun y => ?_
    let x := φ.symm y
    obtain ⟨n, s, hs_nhds, hs_homeo⟩ := h.locally_homeomorph x
    have h_img_mem : φ '' s ∈ 𝓝 y := by
      have h_eq : y = φ x := by simp [x]
      rw [h_eq, ← φ.map_nhds_eq x, Filter.mem_map, φ.preimage_image]
      exact hs_nhds
    have e1 : s ≃ₜ φ '' s := φ.image s
    obtain ⟨e2⟩ := hs_homeo
    exact ⟨n, φ '' s, h_img_mem, ⟨e1.symm.trans e2⟩⟩

end PiBase.Formal
