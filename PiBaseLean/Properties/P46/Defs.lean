module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

namespace PiBase

/- 46. Totally path disconnected -/
class TotallyPathDisconnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  totally_path_disconnected : ∀ f : Icc (0 : ℝ) 1 → X, Continuous f → ∃ x : X, f = const (Icc 0 1) x

end PiBase

namespace PiBase.Formal

def P46 : Property where
  toPred := TotallyPathDisconnectedSpace
  well_defined φ h := by
    constructor
    intro f hf
    -- compose arbitrary path into Y with φ.symm to get path into X
    have hcomp : Continuous (fun t : Icc (0 : ℝ) 1 => φ.symm (f t)) :=
      φ.symm.continuous.comp hf
    -- apply totally path disconnected in X to get constant
    obtain ⟨x, hx⟩ := h.totally_path_disconnected (fun t => φ.symm (f t)) hcomp
    refine ⟨φ x, ?_⟩
    ext t
    simp only [Function.const_apply]
    -- extract pointwise equality from hx : (φ.symm ∘ f) = const x
    have hxt : φ.symm (f t) = x := by
      have := congrFun hx t
      simpa [Function.const_apply] using this
    -- push constant through φ : f t = φ (φ.symm (f t)) = φ x
    calc f t = φ (φ.symm (f t)) := (φ.apply_symm_apply (f t)).symm
      _ = φ x := by rw [hxt]

end PiBase.Formal
