module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P33.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.countablyMetacompactSpace [h : CountablyMetacompactSpace X] (f : X ≃ₜ Y) :
    CountablyMetacompactSpace Y :=
  Formal.P33.well_defined f h

theorem WellDefined.countablyMetacompactSpace : WellDefined CountablyMetacompactSpace :=
  fun {_ _} _ _ h hX => Formal.P33.well_defined h.some hX

end Meta

end PiBase
