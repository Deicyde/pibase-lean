module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P109.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.monotonicallyNormalSpace [h : MonotonicallyNormalSpace X] (f : X ≃ₜ Y) :
    MonotonicallyNormalSpace Y :=
  Formal.P109.well_defined f h

theorem WellDefined.monotonicallyNormalSpace : WellDefined MonotonicallyNormalSpace :=
  fun {_ _} _ _ h _ => Homeomorph.monotonicallyNormalSpace h.some

end Meta

end PiBase
