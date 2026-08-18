module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P34.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.fullyNormalSpace : WellDefined FullyNormalSpace :=
  fun {X Y} _ _ φ _ => @FullyNormalSpace.mk _ _ φ.some.symm.isClosedEmbedding.paracompactSpace φ.some.normalSpace

theorem Homeomorph.fullyNormalSpace [FullyNormalSpace X] (f : X ≃ₜ Y) : FullyNormalSpace Y :=
  WellDefined.fullyNormalSpace ⟨f⟩ inferInstance

end Meta

end PiBase
