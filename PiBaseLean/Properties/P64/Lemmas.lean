module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P64.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.baireSpace : WellDefined BaireSpace :=
  fun {_ _} _ _ h _ ↦ Homeomorph.baireSpace h.some

end Meta

end PiBase
