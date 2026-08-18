module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P164.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace
open Cardinal

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.cardLtEveryMeasurableCardinal [h : CardLtEveryMeasurableCardinal X]
    (f : X ≃ₜ Y) : CardLtEveryMeasurableCardinal Y :=
  Formal.P164.well_defined f h

theorem WellDefined.cardLtEveryMeasurableCardinal :
    WellDefined (fun (X : Type u) => CardLtEveryMeasurableCardinal X) :=
  fun {X Y} [TopologicalSpace X] [TopologicalSpace Y] h _ =>
    Homeomorph.cardLtEveryMeasurableCardinal (X := X) h.some

end Meta

end PiBase
