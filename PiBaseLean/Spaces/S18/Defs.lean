module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Topology.Order
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S18

/- Space 18: Double pointed cocountable topology on ℝ.
See https://topology.pi-base.org/spaces/S000018.
X is the product of the cocountable topology on ℝ (S17) with the indiscrete
topology on a two-point set (S4): a set in ℝ is declared open iff it is empty
or has countable complement, and the product carries the product topology. -/

/-- The cocountable topology on ℝ (pi-Base S17): a set is open iff it is
empty or its complement is countable. -/
def CocountableReal : Type := ℝ

instance : TopologicalSpace CocountableReal :=
  TopologicalSpace.generateFrom {s : Set CocountableReal | s = ∅ ∨ sᶜ.Countable}

/-- The indiscrete topology on a two-point set (pi-Base S4), used here as the
second factor of the product. -/
def Indiscrete2 : Type := Fin 2

instance : TopologicalSpace Indiscrete2 := ⊤

/-- The double pointed cocountable topology on ℝ (pi-Base S18): the product
of the cocountable topology on ℝ (S17) with the indiscrete topology on a
two-point set (S4). -/
def S18 : Type := CocountableReal × Indiscrete2

instance : TopologicalSpace S18 :=
  inferInstanceAs (TopologicalSpace (CocountableReal × Indiscrete2))

end S18
end PiBase.Spaces
