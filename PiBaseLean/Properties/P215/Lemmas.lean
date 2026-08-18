module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P215.Defs
public import PiBaseLean.Properties.P162.Lemmas

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.hereditarilyRealcompactSpace : WellDefined HereditarilyRealcompactSpace :=
  fun hXY hX => ⟨(Hereditarily.wellDefined WellDefined.realcompactSpace) hXY hX.subset_realcompact⟩

end Meta

end PiBase
