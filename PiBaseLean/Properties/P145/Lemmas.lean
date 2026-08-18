module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P145.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.stronglyParacompactSpace [h : StronglyParacompactSpace X] (f : X ≃ₜ Y) :
    StronglyParacompactSpace Y :=
  Formal.P145.well_defined f h

theorem WellDefined.stronglyParacompactSpace : WellDefined StronglyParacompactSpace :=
  fun {_ _} _ _ h hX => Homeomorph.stronglyParacompactSpace h.some

end Meta

end PiBase
