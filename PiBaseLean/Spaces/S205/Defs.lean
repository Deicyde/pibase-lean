module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S205

/- Space 205: Warsaw circle.
See https://topology.pi-base.org/spaces/S000205.
The subspace of ℝ² given by the topologist's sine curve arc
{(x, sin(1/x)) : x ∈ (0,1]} ∪ {(0,y) : y ∈ [-2,1]}, closed up into a loop by an
extra path {(x,-2) : x ∈ [0,1]} ∪ {(1,y) : y ∈ [-2, sin 1]} joining its two loose ends. -/

/-- The carrier set of the Warsaw circle inside `ℝ × ℝ`. -/
def warsawCircleSet : Set (ℝ × ℝ) :=
  (fun x => (x, Real.sin x⁻¹)) '' Set.Ioc (0 : ℝ) 1 ∪
  (fun y => ((0 : ℝ), y)) '' Set.Icc (-2 : ℝ) 1 ∪
  (fun x => (x, (-2 : ℝ))) '' Set.Icc (0 : ℝ) 1 ∪
  (fun y => ((1 : ℝ), y)) '' Set.Icc (-2 : ℝ) (Real.sin 1)

/-- The Warsaw circle (pi-Base S205), as a subset of `ℝ × ℝ`. -/
def S205 : Type := {p : ℝ × ℝ // p ∈ warsawCircleSet}

instance S205_top : TopologicalSpace S205 := instTopologicalSpaceSubtype

end S205
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S205 as a bundled `Space` (carrier + topology). -/
noncomputable def S205 : Space := ⟨PiBase.Spaces.S205.S205, PiBase.Spaces.S205.S205_top⟩

end PiBase.Formal
