module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P146.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.ultraparacompactSpace [h : UltraparacompactSpace X] (f : X ≃ₜ Y) :
    UltraparacompactSpace Y :=
  Formal.P146.well_defined f h

theorem WellDefined.ultraparacompactSpace : WellDefined UltraparacompactSpace :=
  fun {_ _} _ _ h hX => Homeomorph.ultraparacompactSpace h.some

end Meta

end PiBase
