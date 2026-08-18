module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P32.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.countablyParacompactSpace [h : CountablyParacompactSpace X] (f : X ≃ₜ Y) :
    CountablyParacompactSpace Y :=
  Formal.P32.well_defined f h

theorem WellDefined.countablyParacompactSpace : WellDefined CountablyParacompactSpace :=
  fun {_ _} _ _ h hX => Formal.P32.well_defined h.some hX

end Meta

end PiBase
