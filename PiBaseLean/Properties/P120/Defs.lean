module

public import Mathlib.Topology.Homeomorph.Lemmas
public import PiBaseLean.Properties.P133.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 120. Locally orderable -/
class LocallyOrderableSpace (X : Type u) [TopologicalSpace X] : Prop where
  ex_nbhd_lots (x : X) : ∃ s ∈ 𝓝 x, Lots s

end PiBase

namespace PiBase.Formal

def P120 : Property where
  toPred := LocallyOrderableSpace
  well_defined φ h := by
    constructor
    intro y
    obtain ⟨s, hs_mem, hs_lots⟩ := h.ex_nbhd_lots (φ.symm y)
    refine ⟨φ '' s, ?_, ?_⟩
    · rw [← φ.apply_symm_apply y, ← φ.map_nhds_eq (φ.symm y)]
      exact Filter.mem_map.mpr (Filter.mem_of_superset hs_mem (Set.subset_preimage_image φ s))
    · have hHomeo : s ≃ₜ φ '' s := φ.image s
      exact Formal.P133.well_defined hHomeo hs_lots

end PiBase.Formal
