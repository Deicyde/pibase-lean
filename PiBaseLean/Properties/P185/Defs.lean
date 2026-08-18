module

public import Mathlib.Topology.Inseparable
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 185. Partition topology -/
class PartitionTopology (X : Type u) [TopologicalSpace X] : Prop where
  quotient_discrete : DiscreteTopology (SeparationQuotient X)

end PiBase

namespace PiBase.Formal

/-- A homeomorphism `φ : X ≃ₜ Y` descends to a homeomorphism of the Kolmogorov quotients. -/
def separationQuotientCongr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) : SeparationQuotient X ≃ₜ SeparationQuotient Y where
  toFun := SeparationQuotient.lift (fun x => SeparationQuotient.mk (φ x))
    fun _ _ hxy => SeparationQuotient.mk_eq_mk.2 (hxy.map φ.continuous)
  invFun := SeparationQuotient.lift (fun y => SeparationQuotient.mk (φ.symm y))
    fun _ _ hxy => SeparationQuotient.mk_eq_mk.2 (hxy.map φ.symm.continuous)
  left_inv := SeparationQuotient.surjective_mk.forall.2 fun x => by simp
  right_inv := SeparationQuotient.surjective_mk.forall.2 fun y => by simp
  continuous_toFun :=
    SeparationQuotient.continuous_lift (SeparationQuotient.continuous_mk.comp φ.continuous)
  continuous_invFun :=
    SeparationQuotient.continuous_lift (SeparationQuotient.continuous_mk.comp φ.symm.continuous)

def P185 : Property where
  toPred := PartitionTopology
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h :=
    ⟨(separationQuotientCongr φ).discreteTopology_iff.mp h.quotient_discrete⟩

end PiBase.Formal
