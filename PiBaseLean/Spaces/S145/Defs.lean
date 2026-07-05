module

public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Topology.Order

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S145

/- Space 145: Free ultrafilter topology on ω.
See https://topology.pi-base.org/spaces/S000145.
The carrier is `ω = ℕ`; the open sets are `𝒰 ∪ {∅}` for a free ultrafilter `𝒰` on `ℕ`.
We witness `𝒰` by `Filter.hyperfilter ℕ`, the (noncomputable) ultrafilter extending the
cofinite filter, which is free since it contains no finite set (in particular no singleton). -/

/-- Free ultrafilter topology on `ω` (pi-Base S145). -/
def S145 : Type := ℕ

noncomputable instance : TopologicalSpace S145 :=
  TopologicalSpace.generateFrom {S : Set ℕ | S ∈ Filter.hyperfilter ℕ}

end S145
end PiBase.Spaces
