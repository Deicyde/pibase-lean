module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P150.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

universe u

section Meta

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.omegaRothberger [h : OmegaRothberger X] (f : X ≃ₜ Y) : OmegaRothberger Y :=
  Formal.P150.well_defined f h

theorem WellDefined.omegaRothberger : WellDefined OmegaRothberger :=
  fun {_ _} _ _ h hX => Homeomorph.omegaRothberger h.some

end Meta

end PiBase
