module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P227.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace Cardinal

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

-- Transport

-- Transport DiscreteTopology on subtype via subtype homeomorphism,
-- closedness via Homeomorph closed image, cardinal via mk_image_eq.
theorem WellDefined.hasClosedDiscreteSubsetCardContinuum :
    WellDefined HasClosedDiscreteSubsetCardContinuum :=
  fun {_ _} _ _ h hX => PiBase.Formal.P227.well_defined h.some hX

end Meta

end PiBase
