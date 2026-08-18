module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P61.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.cozeroComplementedSpace [h : CozeroComplementedSpace X] (f : X ≃ₜ Y) :
    CozeroComplementedSpace Y :=
  Formal.P61.well_defined f h

theorem WellDefined.cozeroComplementedSpace : WellDefined CozeroComplementedSpace :=
  fun {_ _} _ _ h hX => Homeomorph.cozeroComplementedSpace h.some

end Meta

end PiBase
