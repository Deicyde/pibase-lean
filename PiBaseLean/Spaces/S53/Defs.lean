module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.PNat.Defs
public import Mathlib.Topology.Order

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S53

/- Space 53: Prime integer topology.
See https://topology.pi-base.org/spaces/S000053.
On the positive integers X = ℕ+, generate the topology from the subbasis of all
sets U p b = {x ∈ X : x ≡ b (mod p)} for p prime and b not divisible by p. -/

/-- The prime integer topology (pi-Base S53) is carried by the positive integers `ℕ+`. -/
def S53 : Type := ℕ+

/-- The subbasic set `U p b = {x ∈ X : x ≡ b [MOD p]}` for `p` prime and `p ∤ b`. -/
def subbasis : Set (Set S53) :=
  {s | ∃ p : ℕ, ∃ b : ℕ, p.Prime ∧ ¬ p ∣ b ∧ s = {x : ℕ+ | (x : ℕ) ≡ b [MOD p]}}

instance : TopologicalSpace S53 := TopologicalSpace.generateFrom subbasis

end S53
end PiBase.Spaces
