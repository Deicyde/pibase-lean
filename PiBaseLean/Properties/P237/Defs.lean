module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Separation.Hausdorff
public import PiBaseLean.Properties.P236.Defs

@[expose] public section

universe u

namespace PiBase

open Topology

/- 237. Topological n-manifold with boundary -/
class TopologicalNManifoldWithBoundary (X : Type u) [TopologicalSpace X] extends
  SecondCountableTopology X, T2Space X, LocallyNEuclideanHalfSpace X

end PiBase

namespace PiBase.Formal

def P237 : Property where
  toPred := TopologicalNManifoldWithBoundary
  well_defined φ h :=
    let hT2 : T2Space _ := φ.t2Space
    let hSC : SecondCountableTopology _ := φ.symm.secondCountableTopology
    let hL : LocallyNEuclideanHalfSpace _ :=
      Formal.P236.well_defined φ h.toLocallyNEuclideanHalfSpace
    @TopologicalNManifoldWithBoundary.mk _ _ hSC hT2 hL

end PiBase.Formal
