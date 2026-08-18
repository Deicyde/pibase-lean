module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P231.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.weaklyLocallySimplyConnectedSpace [h : WeaklyLocallySimplyConnectedSpace X]
    (f : X ≃ₜ Y) : WeaklyLocallySimplyConnectedSpace Y :=
  Formal.P231.well_defined f h

theorem WellDefined.weaklyLocallySimplyConnectedSpace :
    WellDefined WeaklyLocallySimplyConnectedSpace :=
  fun {_ _} _ _ h hX => Homeomorph.weaklyLocallySimplyConnectedSpace h.some

end Meta

end PiBase
