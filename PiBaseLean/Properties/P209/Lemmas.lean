module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P209.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace Cardinal

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.densityLeContinuum : WellDefined DensityLeContinuum :=
  fun {_ _} _ _ h hX => Formal.P209.well_defined h.some hX

end Meta

end PiBase
