module

public import Mathlib.Topology.Connected.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

namespace PiBase

/- 234. Has open connected components -/
class HasOpenConnectedComponents (X : Type*) [TopologicalSpace X] : Prop where
  component_open (x : X) : IsOpen (connectedComponent x)

end PiBase

namespace PiBase.Formal

def P234 : Property where
  toPred := HasOpenConnectedComponents
  well_defined φ h := by
    constructor
    intro y
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    set w := φ.symm z with hw_def
    have hzw : z = φ w := (φ.apply_symm_apply z).symm
    have hw_mem : connectedComponent w ∈ nhds w :=
      (h.component_open w).mem_nhds mem_connectedComponent
    have hw_img_mem : φ '' connectedComponent w ∈ nhds z := by
      rw [hzw, ← φ.map_nhds_eq w]
      exact Filter.image_mem_map hw_mem
    refine Filter.mem_of_superset hw_img_mem ?_
    have h_conn : IsConnected (φ '' connectedComponent w) :=
      isConnected_connectedComponent.image φ φ.continuous.continuousOn
    have hz_mem : z ∈ φ '' connectedComponent w :=
      hzw ▸ Set.mem_image_of_mem φ mem_connectedComponent
    have h_sub_z : φ '' connectedComponent w ⊆ connectedComponent z :=
      h_conn.subset_connectedComponent hz_mem
    rwa [connectedComponent_eq_iff_mem.mpr hz] at h_sub_z

end PiBase.Formal
