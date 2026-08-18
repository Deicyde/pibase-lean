module

public import PiBaseLean.Properties.P183.Defs
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Homeomorph.Lemmas
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 179. ℵ₀-space -/
class AlephZeroSpace (X : Type u) [TopologicalSpace X] : Prop extends
    T3Space X, HasCountableKNetwork X

end PiBase

namespace PiBase.Formal

def P179 : Property where
  toPred := AlephZeroSpace
  well_defined φ h := by
    -- Preserve both parent classes under homeomorphism
    -- This reuses the compiled P183 well-defined lemma
    have hT3 : T3Space _ := φ.t3Space
    have hK : HasCountableKNetwork _ := PiBase.Formal.P183.well_defined φ h.toHasCountableKNetwork
    exact { hK with }

end PiBase.Formal
