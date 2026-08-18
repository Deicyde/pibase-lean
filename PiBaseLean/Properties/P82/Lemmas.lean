module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P82.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallyMetrizableSpace [h : LocallyMetrizableSpace X]
    (f : X ≃ₜ Y) : LocallyMetrizableSpace Y :=
  Formal.P82.well_defined f h

theorem WellDefined.locallyMetrizableSpace : WellDefined LocallyMetrizableSpace :=
  fun {_ _} _ _ h hX => Homeomorph.locallyMetrizableSpace h.some

end Meta

end PiBase
