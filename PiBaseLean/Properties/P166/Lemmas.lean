module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P166.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.hasCoarserSeparableMetrizableTopology
    [h : HasCoarserSeparableMetrizableTopology X] (f : X ≃ₜ Y) :
    HasCoarserSeparableMetrizableTopology Y :=
  Formal.P166.well_defined f h

theorem WellDefined.hasCoarserSeparableMetrizableTopology :
    WellDefined HasCoarserSeparableMetrizableTopology :=
  fun {_ _} _ _ h _ => Homeomorph.hasCoarserSeparableMetrizableTopology h.some

end Meta

end PiBase
