module

public import Mathlib.Topology.Instances.Rat
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Data.Rat.Denumerable

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S80

/- Space 80: B. Scott's modified Arens square.
See https://topology.pi-base.org/spaces/S000080.
`Q = (0,1) ∩ ℚ`, split (via a fixed pairing bijection `Q ≃ Q × Q`) into the family
`{Qpart q}_{q : Q}` of fibers of the second projection — a genuine partition of `Q`
indexed by `Q` itself, matching π-Base's `{Q_q : q ∈ Q}` (density of each part is
asserted by π-Base but not reproved here; see the TODO on `Qpart`).
`S = ⋃ q, {q} × Qpart q ⊆ Q × Q`, and `X = {(0,0),(1,0)} ∪ S`. Away from
`M = {1/2} × Qpart 1/2`, points of `S` keep their inherited Euclidean neighborhoods;
`(0,0)`, `(1,0)` and the points of `M` instead get the special local bases `Uₙ` from
π-Base, so the topology is generated from the union of both subbasic families. -/

/-- `Q`, the rationals in the open interval `(0, 1)`. -/
def S80.Q : Type := ↥(Set.Ioo (0 : ℚ) 1)

instance : Infinite S80.Q := Set.Ioo.infinite (by norm_num)

instance : Encodable S80.Q := inferInstanceAs (Encodable ↥(Set.Ioo (0 : ℚ) 1))

noncomputable instance : Denumerable S80.Q := Denumerable.ofEncodableOfInfinite S80.Q

/-- A fixed pairing bijection witnessing that `Q` splits into countably many parts
indexed by `Q` itself. -/
noncomputable def S80.pairEquiv : S80.Q × S80.Q ≃ S80.Q := Denumerable.pair

/-- `Qpart q`, the part of the partition of `Q` associated with `q : Q`: the fiber over
`q` of the second projection of `S80.pairEquiv.symm`. This is a genuine partition of
`Q` indexed by `Q` (every `q' : Q` lies in exactly one `Qpart q`), matching π-Base's
`{Q_q : q ∈ Q}`.
TODO: π-Base additionally asserts each `Qpart q` is *dense* in `Q`; that density is not
reproved here (it plays no role in defining the carrier or the topology below, only in
justifying the space's separation properties). -/
noncomputable def S80.Qpart (q : S80.Q) : Set S80.Q :=
  {q' : S80.Q | (S80.pairEquiv.symm q').2 = q}

/-- The point `1/2 ∈ Q`. -/
def S80.half : S80.Q := ⟨1 / 2, by norm_num⟩

/-- The carrier `X = {(0,0), (1,0)} ∪ S` where `S = ⋃ q, {q} × Qpart q ⊆ Q × Q`,
viewed inside `ℚ × ℚ` (with `(0,0)` and `(1,0)` the two adjoined corner points). -/
noncomputable def S80.carrier : Set (ℚ × ℚ) :=
  {(0, 0), (1, 0)} ∪ {p : ℚ × ℚ | ∃ q : S80.Q, ∃ y ∈ S80.Qpart q, p = (q.1, y.1)}

/-- B. Scott's modified Arens square (pi-Base S80). -/
noncomputable def S80 : Type := ↥S80.carrier

namespace S80

/-- The distinguished point `(0,0) ∈ X`. -/
noncomputable def corner0 : S80 := ⟨(0, 0), Or.inl (Or.inl rfl)⟩

/-- The distinguished point `(1,0) ∈ X`. -/
noncomputable def corner1 : S80 := ⟨(1, 0), Or.inl (Or.inr rfl)⟩

/-- `M = {1/2} × Qpart (1/2)`, viewed as a subset of `S80`. -/
noncomputable def M : Set S80 := {x : S80 | x.1.1 = half.1}

/-- The basic Euclidean-inherited neighbourhood of a point `p : ℚ × ℚ`, radius `ε`:
the open Euclidean ball around `p` intersected with the carrier `X`. Used as the local
basis at points of `S \ M`. -/
def ballNbhd (p : ℚ × ℚ) (ε : ℝ) : Set S80 := {x : S80 | dist x.1 p < ε}

/-- The local basis `Uₙ(0,0) = {(0,0)} ∪ {(x,y) ∈ S : 0<x<1/4, 0<y<1/n}` at the
corner point `(0,0)`. -/
def U0 (n : ℕ) : Set S80 :=
  {corner0} ∪
    {x : S80 | 0 < x.1.1 ∧ x.1.1 < 1 / 4 ∧ 0 < x.1.2 ∧ x.1.2 < 1 / (n : ℚ)}

/-- The local basis `Uₙ(1,0) = {(1,0)} ∪ {(x,y) ∈ S : 3/4<x<1, 0<y<1/n}` at the
corner point `(1,0)`. -/
def U1 (n : ℕ) : Set S80 :=
  {corner1} ∪
    {x : S80 | 3 / 4 < x.1.1 ∧ x.1.1 < 1 ∧ 0 < x.1.2 ∧ x.1.2 < 1 / (n : ℚ)}

/-- The local basis `Uₙ(1/2, q) = {(x,y) ∈ S : 1/4<x<3/4, q-1/n<y<q+1/n}` at a point
`(1/2, q) ∈ M`. -/
def UM (q : S80.Q) (n : ℕ) : Set S80 :=
  {x : S80 | 1 / 4 < x.1.1 ∧ x.1.1 < 3 / 4 ∧
    q.1 - 1 / (n : ℚ) < x.1.2 ∧ x.1.2 < q.1 + 1 / (n : ℚ)}

end S80

/-- The topology on `X`, generated from: the Euclidean-inherited balls (local basis on
`S \ M`), together with the special local bases `Uₙ(0,0)`, `Uₙ(1,0)` and `Uₙ(1/2,q)` for
`q` ranging over `Qpart (1/2)` (local bases at the corner points and at `M`). -/
noncomputable instance : TopologicalSpace S80 :=
  TopologicalSpace.generateFrom
    ({s : Set S80 | ∃ (p : ℚ × ℚ) (ε : ℝ), ε > 0 ∧ s = S80.ballNbhd p ε} ∪
      {s : Set S80 | ∃ n : ℕ, s = S80.U0 n} ∪
      {s : Set S80 | ∃ n : ℕ, s = S80.U1 n} ∪
      {s : Set S80 | ∃ (q : S80.Q) (n : ℕ), q ∈ S80.Qpart S80.half ∧ s = S80.UM q n})

end S80
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S80 as a bundled `Space` (carrier + topology). -/
noncomputable def S80 : Space := ⟨PiBase.Spaces.S80.S80, inferInstance⟩

end PiBase.Formal
