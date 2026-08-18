module

public import PiBaseLean.Properties.P117.Defs
public import Mathlib.Topology.Separation.Regular

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 177. σ-space -/
class SigmaSpace (X : Type u) [TopologicalSpace X] : Prop extends
    T3Space X, HasSigmaLocallyFiniteNetwork X

end PiBase

namespace PiBase.Formal

def P177 : Property where
  toPred := SigmaSpace
  well_defined φ h := by
    have : T3Space _ := φ.t3Space
    have : HasSigmaLocallyFiniteNetwork _ :=
      P117.well_defined φ h.toHasSigmaLocallyFiniteNetwork
    exact ⟨⟩

end PiBase.Formal
