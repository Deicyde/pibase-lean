module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P192.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.quasiSober [h : QuasiSober X] (φ : X ≃ₜ Y) : QuasiSober Y :=
  Formal.P192.well_defined φ h

theorem WellDefined.quasiSober : WellDefined QuasiSober :=
  fun {_ _} _ _ h _ => Homeomorph.quasiSober h.some

end Meta

end PiBase
