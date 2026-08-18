module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Defs.Induced
public import PiBaseLean.Properties.Bundled.Defs
public import PiBaseLean.AdditionalDefs.Meta

@[expose] public section

universe u

namespace PiBase

open Topology Filter Set Function

/- 241. Locally a Euclidean half-line -/
class LocallyEuclideanHalfLine (X : Type u) [TopologicalSpace X] : Prop where
  locally_homeomorph (x : X): ∃ s ∈ 𝓝 x, ∃ f : s → NNReal, IsOpenEmbedding f

end PiBase

namespace PiBase.Formal

open Topology

def P241 : Property where
  toPred := LocallyEuclideanHalfLine
  well_defined φ h := by
    refine @LocallyEuclideanHalfLine.mk _ _ fun y => ?_
    let x := φ.symm y
    obtain ⟨s, hs, f, hf⟩ := h.locally_homeomorph x
    have h_img_mem : φ '' s ∈ 𝓝 y := by
      have hy : y = φ x := by simp [x]
      rw [hy, ← φ.map_nhds_eq x, Filter.mem_map, φ.preimage_image]
      exact hs
    have e : s ≃ₜ φ '' s := φ.image s
    exact ⟨φ '' s, h_img_mem, f ∘ e.symm, hf.comp e.symm.isOpenEmbedding⟩

end PiBase.Formal
