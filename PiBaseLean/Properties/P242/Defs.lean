module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

universe u

namespace PiBase

/- 242. Weakly contractible -/
class WeaklyContractibleSpace (X : Type u) [TopologicalSpace X] : Prop where
  nonempty : Nonempty X
  homotopically_trivial (x : X) (N : Type) : Finite N → Subsingleton (HomotopyGroup N X x)

end PiBase

namespace PiBase.Formal

open scoped unitInterval Topology Topology.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {N : Type*}

/-- Postcomposition of a generalized loop based at `x` with a continuous map taking `x` to `y`. -/
def genLoopMap (f : C(X, Y)) {x : X} {y : Y} (hf : f x = y) : Ω^ N X x → Ω^ N Y y := fun p =>
  ⟨f.comp (p : C(I^N, X)), fun t ht => by
    rw [ContinuousMap.comp_apply, p.2 t ht, hf]⟩

@[simp]
theorem genLoopMap_coe (f : C(X, Y)) {x : X} {y : Y} (hf : f x = y) (p : Ω^ N X x) :
    ((genLoopMap f hf p : Ω^ N Y y) : C(I^N, Y)) = f.comp (p : C(I^N, X)) := rfl

/-- The map on homotopy groups induced by postcomposition with a continuous map taking the base
point `x` to the base point `y`. -/
def homotopyGroupMap (f : C(X, Y)) {x : X} {y : Y} (hf : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.lift (fun p => ⟦genLoopMap f hf p⟧) fun _ _ hab =>
    Quotient.sound (ContinuousMap.HomotopicRel.comp_continuousMap hab f)

@[simp]
theorem homotopyGroupMap_mk (f : C(X, Y)) {x : X} {y : Y} (hf : f x = y) (p : Ω^ N X x) :
    homotopyGroupMap (N := N) f hf ⟦p⟧ = ⟦genLoopMap f hf p⟧ := rfl

/-- A homeomorphism induces a surjection on homotopy groups: postcomposition with `φ.symm`
provides a section. -/
theorem homotopyGroupMap_surjective (φ : X ≃ₜ Y) (y : Y) :
    Function.Surjective (homotopyGroupMap (N := N) (φ : C(X, Y)) (φ.apply_symm_apply y)) := by
  refine Quotient.ind fun q => ⟨⟦genLoopMap (φ.symm : C(Y, X)) rfl q⟧, ?_⟩
  rw [homotopyGroupMap_mk]
  congr 1
  refine Subtype.ext (ContinuousMap.ext fun t => ?_)
  simp

def P242 : Property where
  toPred := WeaklyContractibleSpace
  well_defined {X Y} _ _ φ h :=
  { nonempty := h.nonempty.elim fun x => ⟨φ x⟩
    homotopically_trivial := fun y N hFin => by
      have hSub : Subsingleton (HomotopyGroup N X (φ.symm y)) :=
        h.homotopically_trivial (φ.symm y) N hFin
      exact (homotopyGroupMap_surjective (N := N) φ y).subsingleton }

end PiBase.Formal
