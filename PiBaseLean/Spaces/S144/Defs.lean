module

public import Mathlib.Topology.Order

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S144

/- Space 144: Diamond poset 2×2 with Alexandrov topology.
See https://topology.pi-base.org/spaces/S000144.
Carrier `P = {0, a, b, 1}` (encoded as `Fin 4` via `0 ↦ 0`, `a ↦ 1`, `b ↦ 2`, `1 ↦ 3`),
the four-element poset with `0` least, `1` greatest, and `a, b` incomparable. The
Alexandrov topology has as open sets exactly the upper sets of this order; we generate
it from the four principal up-sets `↑0 = P`, `↑a = {a,1}`, `↑b = {b,1}`, `↑1 = {1}`,
whose unions are exactly the up-sets of the diamond. -/

/-- The carrier of the diamond poset `2×2` (pi-Base S144): the four elements
`{0, a, b, 1}`, encoded as `Fin 4` with `0 ↦ 0`, `a ↦ 1`, `b ↦ 2`, `1 ↦ 3`. -/
def S144 : Type := Fin 4

/-- The four principal up-sets of the diamond order: `↑0 = P`, `↑a = {a,1}`,
`↑b = {b,1}`, `↑1 = {1}`. Generating the topology from these gives exactly the
up-sets of the diamond poset (the empty union `∅`, each principal up-set, their
pairwise union `{a,b,1}`, and the full union `P`). -/
def S144.generators : Set (Set S144) :=
  { ({((0 : Fin 4) : S144), ((1 : Fin 4) : S144), ((2 : Fin 4) : S144), ((3 : Fin 4) : S144)}
      : Set S144),
    ({((1 : Fin 4) : S144), ((3 : Fin 4) : S144)} : Set S144),
    ({((2 : Fin 4) : S144), ((3 : Fin 4) : S144)} : Set S144),
    ({((3 : Fin 4) : S144)} : Set S144) }

instance : TopologicalSpace S144 := TopologicalSpace.generateFrom S144.generators

end S144
end PiBase.Spaces
