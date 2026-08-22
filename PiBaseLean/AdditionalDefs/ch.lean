module

public import Mathlib.Analysis.Real.Cardinality
public import PiBaseLean.Theorems.T21.Theorem

import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.UnitInterval

open Cardinal

/-- The continuum hypothesis. -/
def ContinuumHypothesis : Prop := (𝔠 : Cardinal.{0}) = ℵ₁

/-- The generalized continuum hypothesis on `Type 0`.
(For this question, we can ignore the exact implementation) -/
def GeneralizedContinuumHypothesis : Prop :=
  ∀ o : Ordinal.{0}, ℵ₀ ≤ ℵ_ o → ℵ_ (o + 1) = 2 ^ (ℵ_ o)

theorem unprovable : ¬ (ContinuumHypothesis → GeneralizedContinuumHypothesis) := by
  simp?
  sorry
