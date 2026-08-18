module

public import Mathlib.Topology.Connected.PathConnected
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

namespace PiBase

/- 233. Has open path components -/
class HasOpenPathComponents (X : Type*) [TopologicalSpace X] : Prop where
  component_open (x : X) : IsOpen (pathComponent x)

end PiBase

namespace PiBase.Formal

def P233 : Property where
  toPred := HasOpenPathComponents
  well_defined φ h := by
    -- pathComponent x is an open nhd in X, its image is a path-connected nhd in Y,
    -- hence Y has open path components.
    constructor
    intro y
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    set w := φ.symm z with hw_def
    have hzw : z = φ w := (φ.apply_symm_apply z).symm
    have hw_mem : pathComponent w ∈ nhds w :=
      (h.component_open w).mem_nhds (mem_pathComponent_self w)
    have hw_img_mem : φ '' pathComponent w ∈ nhds z := by
      rw [hzw, ← φ.map_nhds_eq w]
      exact Filter.image_mem_map hw_mem
    refine Filter.mem_of_superset hw_img_mem ?_
    have h_pc : IsPathConnected (φ '' pathComponent w) :=
      φ.isPathConnected_image.mpr isPathConnected_pathComponent
    have hz_mem : z ∈ φ '' pathComponent w :=
      hzw ▸ Set.mem_image_of_mem φ (mem_pathComponent_self w)
    have h_sub_z : φ '' pathComponent w ⊆ pathComponent z :=
      h_pc.subset_pathComponent hz_mem
    rwa [pathComponent_congr hz] at h_sub_z

end PiBase.Formal
