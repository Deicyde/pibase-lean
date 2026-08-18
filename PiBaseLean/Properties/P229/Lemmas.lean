module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P229.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.semilocallySimplyConnectedSpace (f : X ≃ₜ Y)
    [SemilocallySimplyConnectedSpace X] : SemilocallySimplyConnectedSpace Y :=
  semilocallySimplyConnectedSpace_of_homeomorph f inferInstance

theorem WellDefined.semilocallySimplyConnectedSpace : WellDefined SemilocallySimplyConnectedSpace :=
  fun {_ _} _ _ h _ => Homeomorph.semilocallySimplyConnectedSpace h.some

end Meta

end PiBase
