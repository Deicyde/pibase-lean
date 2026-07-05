module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.PNat.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S56

/- Space 56: Smirnov's deleted sequence topology.
See https://topology.pi-base.org/spaces/S000056.
Let `K = {1/n : n ∈ ℕ}`. The topology on `ℝ` consists of all sets `U \ B` where `U` is
open in the standard topology and `B ⊆ K`. -/

/-- The set `K = {1/n : n ∈ ℕ}` (pi-Base's `ℕ` excludes `0`) used to define the
deleted sequence topology. -/
def S56.K : Set ℝ := {x : ℝ | ∃ n : ℕ+, x = 1 / (n : ℝ)}

/-- Smirnov's deleted sequence topology (pi-Base S56), also known as the K-topology. -/
def S56 : Type := ℝ

instance : TopologicalSpace S56 :=
  TopologicalSpace.generateFrom
    {s : Set ℝ | ∃ U : Set ℝ, IsOpen U ∧ ∃ B ⊆ S56.K, s = U \ B}

end S56
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S56 as a bundled `Space` (carrier + topology). -/
noncomputable def S56 : Space := ⟨PiBase.Spaces.S56.S56, inferInstance⟩

end PiBase.Formal
