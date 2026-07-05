module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S132

/- Space 132: Duncan's space.
See https://topology.pi-base.org/spaces/S000132.
`A` is the type of strictly increasing sequences of positive integers. For `x : A` and
`n : ℕ`, `N n x` counts the indices `i` with `x i < n`, and `δ x` is
`limₙ N n x / n` (when this limit exists). `X` is the subtype of `A` on which `δ`
exists. For `x y : X`, `k x y` is the least index where `x` and `y` disagree (when
`x ≠ y`), and `d x y = 1 / k x y + |δ x - δ y|` (with `d x x = 0`). Duncan's space is
the topology on `X` induced by this distance function `d`, generated here from its
open balls. -/

/-- `A`: the type of strictly increasing, infinite sequences of positive integers. -/
def S132.A : Type := {x : ℕ → ℕ+ // StrictMono x}

/-- `N n x`: the number of indices `i` with `x i < n` (as positive integers). -/
noncomputable def S132.N (n : ℕ) (x : S132.A) : ℕ := {i : ℕ | (x.1 i : ℕ) < n}.ncard

/-- The asymptotic density `δ x = limₙ→∞ (N n x) / n` exists for `x : A`. -/
def S132.HasDensity (x : S132.A) : Prop :=
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (S132.N n x : ℝ) / (n : ℝ)) Filter.atTop (nhds L)

/-- `X`: the subtype of `A` on which the asymptotic density `δ` exists. -/
def S132.X : Type := {x : S132.A // S132.HasDensity x}

/-- The asymptotic density `δ x`, for `x : X`, chosen as a limit witness of
`HasDensity`. -/
noncomputable def S132.delta (x : S132.X) : ℝ := x.2.choose

theorem S132.delta_spec (x : S132.X) :
    Filter.Tendsto (fun n : ℕ => (S132.N n x.1 : ℝ) / (n : ℝ)) Filter.atTop (nhds (S132.delta x)) :=
  x.2.choose_spec

/-- `k x y`: the smallest index at which `x` and `y` (viewed as sequences) disagree,
for `x ≠ y`. -/
noncomputable def S132.k (x y : S132.X) (h : x ≠ y) : ℕ :=
  Nat.find (p := fun i => x.1.1 i ≠ y.1.1 i)
    (by
      by_contra hne
      push Not at hne
      exact h (Subtype.ext (Subtype.ext (funext hne))))

open scoped Classical in
/-- The distance function `d x y = 1 / k(x,y) + |δ x - δ y|`, with `d x x = 0`, as
postulated by π-Base's definition of Duncan's space. -/
noncomputable def S132.d (x y : S132.X) : ℝ :=
  if h : x = y then 0
  else 1 / (S132.k x y h : ℝ) + |S132.delta x - S132.delta y|

/-- The open `d`-ball of radius `ε` around `p : X`. -/
def S132.ball (p : S132.X) (ε : ℝ) : Set S132.X := {q : S132.X | S132.d p q < ε}

/-- Duncan's space (pi-Base S132): the set `X` of strictly increasing sequences of
positive integers admitting an asymptotic density, with the topology induced by the
metric `d`. -/
def S132 : Type := S132.X

/-- The topology on `X`, generated from the open balls of the distance function `d`. -/
instance : TopologicalSpace S132 :=
  TopologicalSpace.generateFrom {s : Set S132.X | ∃ (p : S132.X) (ε : ℝ), s = S132.ball p ε}

end S132
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S132 as a bundled `Space` (carrier + topology). -/
noncomputable def S132 : Space := ⟨PiBase.Spaces.S132.S132, inferInstance⟩

end PiBase.Formal
