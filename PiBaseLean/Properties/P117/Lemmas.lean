module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P117.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.hasSigmaLocallyFiniteNetwork [h : HasSigmaLocallyFiniteNetwork X] (f : X ≃ₜ Y) :
    HasSigmaLocallyFiniteNetwork Y :=
  Formal.P117.well_defined f h

theorem WellDefined.hasSigmaLocallyFiniteNetwork : WellDefined HasSigmaLocallyFiniteNetwork :=
  fun {_ _} _ _ h _ => Homeomorph.hasSigmaLocallyFiniteNetwork h.some

end Meta

end PiBase
