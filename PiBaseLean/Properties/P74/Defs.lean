module

public import Mathlib.Topology.Separation.Regular
public import PiBaseLean.Properties.P182.Defs
public import PiBaseLean.Properties.P5.Defs

@[expose] public section

universe u

namespace PiBase

/- 74. Cosmic -/
class CosmicSpace (X : Type u) [TopologicalSpace X] : Prop extends
  T3Space X, HasCountableNetwork X

end PiBase

namespace PiBase.Formal

def P74 : Property where
  toPred := CosmicSpace
  well_defined φ h :=
    @CosmicSpace.mk _ _ (Formal.P5.well_defined φ h.toT3Space)
      (Formal.P182.well_defined φ h.toHasCountableNetwork)

end PiBase.Formal
