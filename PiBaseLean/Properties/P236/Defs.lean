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

/- 236. Locally an n-Euclidean half-space -/
class LocallyNEuclideanHalfSpace (X : Type u) [TopologicalSpace X] : Prop where
  locally_homeomorph : ∃ n : ℕ, ∀ x : X, ∃ U ∈ 𝓝 x, ∃ (f : U → Fin n → NNReal), IsOpenEmbedding f

end PiBase

namespace PiBase.Formal

open Topology

def P236 : Property where
  toPred := LocallyNEuclideanHalfSpace
  well_defined φ h := by
    obtain ⟨n, hn⟩ := h.locally_homeomorph
    refine @LocallyNEuclideanHalfSpace.mk _ _ ⟨n, fun y => ?_⟩
    let x := φ.symm y
    obtain ⟨U, hU, f, hf⟩ := hn x
    have h_img_mem : φ '' U ∈ 𝓝 y := by
      have hy : y = φ x := by simp [x]
      rw [hy, ← φ.map_nhds_eq x, Filter.mem_map, φ.preimage_image]
      exact hU
    have e : U ≃ₜ φ '' U := φ.image U
    exact ⟨φ '' U, h_img_mem, f ∘ e.symm, hf.comp e.symm.isOpenEmbedding⟩

end PiBase.Formal
