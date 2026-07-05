module

public import Mathlib.Topology.Basic
public import Mathlib.Topology.Instances.Discrete

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S172

/- Space 172: Kannan-Rajagopalan-Hart Space.
See https://topology.pi-base.org/spaces/S000172.
pi-Base gives no explicit carrier/topology here, only a pointer to K.P. Hart's
MathOverflow answer (mo:434266), showing that a suitable modification of a Kannan-Rajagopalan
construction (Kannan, Rajagopalan, "Constructions and applications of rigid spaces, I",
Adv. Math. 29 (1978), doi:10.1016/0001-8708(78)90006-3) yields, in ZFC, an infinite,
Hausdorff space with only countably many continuous self-maps. Reconstructing the actual
(highly nontrivial, set-theoretic) topology from that prose answer is out of scope here, so
this file honestly records only the facts pi-Base states outright about the underlying set:
it is infinite (¬P78) and the literature's construction is on a countable set.
-- TODO: replace with Hart's actual topology once reconstructed from mo:434266 /
-- Kannan-Rajagopalan (1978); the discrete topology used below is a faithful carrier but a
-- KNOWN-WRONG topology (discrete spaces have uncountably many continuous self-maps as soon
-- as the carrier is countably infinite, e.g. every permutation), recorded only as a
-- placeholder pending that reconstruction. -/

/-- Kannan-Rajagopalan-Hart Space (pi-Base S172). Carrier only: pi-Base does not specify an
explicit underlying set beyond the source construction being on a countably infinite set. -/
def S172 : Type := ℕ

/-- TODO: placeholder topology only (discrete on the countable carrier) — this is NOT
Hart's actual topology, which is not reconstructed here for lack of an explicit definition
in the pi-Base source data (see the module doc above). In particular this placeholder does
NOT satisfy P138 (countably many continuous self-maps): flagged, not claimed. -/
instance : TopologicalSpace S172 := ⊥

end S172
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S172 as a bundled `Space` (carrier + topology). -/
noncomputable def S172 : Space := ⟨PiBase.Spaces.S172.S172, inferInstance⟩

end PiBase.Formal
