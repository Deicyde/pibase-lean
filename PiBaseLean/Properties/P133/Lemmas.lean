module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P133.Defs
public import Mathlib.Topology.Connected.PathConnected

@[expose] public section

namespace PiBase

open Topology Filter Set TopologicalSpace

variable {X Y : Type u} [t : TopologicalSpace X] [s : TopologicalSpace Y]

theorem Homeomorph.lots [h : Lots X] (f : X ≃ₜ Y) : Lots Y :=
  Formal.P133.well_defined (X := X) (Y := Y) f h

section Meta

theorem WellDefined.lots : WellDefined Lots :=
  fun {_ _} _ _ hXY hX => Homeomorph.lots hXY.some

end Meta

end PiBase
