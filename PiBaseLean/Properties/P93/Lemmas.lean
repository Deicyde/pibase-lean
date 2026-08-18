module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P93.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallyCountableSpace [h : LocallyCountableSpace X] (f : X ≃ₜ Y) : LocallyCountableSpace Y :=
  Formal.P93.well_defined f h

theorem WellDefined.locallyCountableSpace : WellDefined LocallyCountableSpace :=
  fun {_ _} _ _ h hX => Homeomorph.locallyCountableSpace h.some

end Meta

end PiBase
