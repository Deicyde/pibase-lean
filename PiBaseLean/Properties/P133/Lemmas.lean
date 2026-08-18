module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P133.Defs
public import Mathlib.Topology.Connected.PathConnected

@[expose] public section

namespace PiBase

open Topology Filter Set TopologicalSpace

variable {X Y : Type u} [t : TopologicalSpace X] [s : TopologicalSpace Y]

instance instLotsOfOrderTopology {X : Type*} [TopologicalSpace X] [h : LinearOrder X]
    [h' : OrderTopology X] : Lots X where from_linear_order := ⟨h, h'⟩

section Meta

theorem WellDefined.lots : WellDefined Lots :=
  fun {_ _} _ _ hXY hX => Formal.P133.well_defined hXY.some hX

end Meta

end PiBase
