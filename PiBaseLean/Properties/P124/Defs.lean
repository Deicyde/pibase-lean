module

public import PiBaseLean.Properties.P123.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 124. Topological n-manifold -/
class TopologicalNManifold (X : Type u) [TopologicalSpace X] : Prop extends
  LocallyNEuclideanSpace X, T2Space X, SecondCountableTopology X

end PiBase

namespace PiBase.Formal

def P124 : Property where
  toPred := TopologicalNManifold
  well_defined φ h := by
    have hT2 : T2Space _ := φ.t2Space
    have hSC : SecondCountableTopology _ := φ.symm.secondCountableTopology
    obtain ⟨n, hn⟩ := h.locally_homeomorph
    refine @TopologicalNManifold.mk _ _ ⟨n, fun y => ?_⟩ hT2 hSC
    let x := φ.symm y
    obtain ⟨s, hs_nhds, hs_homeo⟩ := hn x
    have h_img_mem : φ '' s ∈ 𝓝 y := by
      have h_eq : y = φ x := by simp [x]
      rw [h_eq, ← φ.map_nhds_eq x, Filter.mem_map, φ.preimage_image]
      exact hs_nhds
    have e1 : s ≃ₜ φ '' s := φ.image s
    obtain ⟨e2⟩ := hs_homeo
    exact ⟨φ '' s, h_img_mem, ⟨e1.symm.trans e2⟩⟩

end PiBase.Formal
