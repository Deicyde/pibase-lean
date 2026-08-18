module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P31.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.metacompactSpace [h : MetacompactSpace X] (f : X ≃ₜ Y) :
    MetacompactSpace Y :=
  Formal.P31.well_defined f h

theorem WellDefined.metacompactSpace : WellDefined MetacompactSpace :=
  fun {_ _} _ _ h hX => Formal.P31.well_defined h.some hX

end Meta

end PiBase
