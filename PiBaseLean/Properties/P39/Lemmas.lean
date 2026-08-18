module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P39.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.preirreducibleSpace [PreirreducibleSpace X] (f : X ≃ₜ Y) : PreirreducibleSpace Y :=
  f.surjective.preirreducibleSpace f.continuous

theorem WellDefined.preirreducibleSpace : WellDefined PreirreducibleSpace :=
  fun {_ _} _ _ h _ => Homeomorph.preirreducibleSpace h.some

end Meta

end PiBase
