module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P118.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.hasSigmaLocallyFiniteKNetwork [h : HasSigmaLocallyFiniteKNetwork X] (f : X ≃ₜ Y) :
    HasSigmaLocallyFiniteKNetwork Y :=
  Formal.P118.well_defined f h

theorem WellDefined.hasSigmaLocallyFiniteKNetwork : WellDefined HasSigmaLocallyFiniteKNetwork :=
  fun {_ _} _ _ h _ => Homeomorph.hasSigmaLocallyFiniteKNetwork h.some

end Meta

end PiBase
