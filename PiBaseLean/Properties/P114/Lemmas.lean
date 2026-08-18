module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P114.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

theorem WellDefined.cardEqAlephOne : WellDefined (fun (X : Type u) => CardEqAlephOne X) :=
  fun {_ _} _ _ h hX => Formal.P114.well_defined h.some hX

end Meta

end PiBase
