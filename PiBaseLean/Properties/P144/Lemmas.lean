module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P144.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locallyPseudoMetrizableSpace [h : LocallyPseudoMetrizableSpace X] (f : X ≃ₜ Y) :
    LocallyPseudoMetrizableSpace Y :=
  Formal.P144.well_defined f h

theorem WellDefined.locallyPseudoMetrizableSpace : WellDefined LocallyPseudoMetrizableSpace :=
  fun {_ _} _ _ h hX => Homeomorph.locallyPseudoMetrizableSpace h.some

end Meta

end PiBase
