module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P164.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace
open Cardinal

section Meta

universe u

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.cardLtEveryMeasurableCardinal :
    WellDefined (fun (X : Type u) => CardLtEveryMeasurableCardinal X) :=
  fun {_ _} _ _ h hX => Formal.P164.well_defined h.some hX

end Meta

end PiBase
