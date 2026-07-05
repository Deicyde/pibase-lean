module

public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S171

/- Space 171: Brian's Example.
See https://topology.pi-base.org/spaces/S000171.
pi-Base gives no explicit carrier/topology, only a pointer to Will Brian's MathOverflow
answer (mo:416331) constructing, in ZFC, an uncountable, Hausdorff, first-countable,
scattered, Lindelöf space whose topology refines that of the reals (P166: "refines {S25}").
Reconstructing the actual (finer) topology from that prose answer is out of scope here, so
this file honestly records only the one carrier/topology fact pi-Base states outright: the
underlying set is (in bijection with) ℝ and the space carries a topology at least as fine as
the Euclidean one.
-- TODO: replace with Brian's actual finer topology once reconstructed from mo:416331. -/

/-- Brian's Example (pi-Base S171). Carrier only: pi-Base does not specify an explicit
underlying set beyond noting it is uncountable and topologically comparable to ℝ (P166). -/
def S171 : Type := ℝ

/-- TODO: this is only the Euclidean topology on ℝ, i.e. a LOWER BOUND on the actual space —
pi-Base states (P166) that Brian's true topology is strictly finer than this one. The finer
topology from mo:416331 is not reconstructed here for lack of an explicit definition in the
pi-Base source data. -/
instance : TopologicalSpace S171 := (inferInstance : TopologicalSpace ℝ)

end S171
end PiBase.Spaces
