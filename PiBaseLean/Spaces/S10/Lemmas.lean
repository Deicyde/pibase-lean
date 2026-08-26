module

public import PiBaseLean.Spaces.Constructions.Sierpinski.Lemmas
public import PiBaseLean.Spaces.S10.Defs

-- BEGIN PIBASE TRAIT IMPORTS
public meta import PiBaseLean.Audit.Spaces.Registry
public import PiBaseLean.Properties.P1.Defs
public import PiBaseLean.Properties.P51.Defs
public import PiBaseLean.Properties.P73.Defs
public import PiBaseLean.Properties.P126.Defs
public import PiBaseLean.Properties.P176.Defs
public import PiBaseLean.Properties.P192.Defs
public import PiBaseLean.Properties.P204.Defs
public import PiBaseLean.Properties.P205.Defs
public import PiBaseLean.Theorems.T143.Theorem
public import PiBaseLean.Theorems.T430.Theorem
public import PiBaseLean.Theorems.T511.Theorem
public import PiBaseLean.Theorems.T558.Theorem
public import PiBaseLean.Theorems.T572.Theorem
public import PiBaseLean.Theorems.T573.Theorem
public import PiBaseLean.Theorems.T635.Theorem
public import PiBaseLean.Theorems.T865.Theorem
-- END PIBASE TRAIT IMPORTS

@[expose] public section

namespace PiBase.Formal

/-! ## Direct catalog traits -/

theorem S10_P125 : P125 PiBase.S10 :=
  P125.well_defined PiBase.S10_canonicalHomeomorph.symm
    (show Nontrivial PiBase.SpaceConstructions.Sierpinski from inferInstance)

register_certificate S000010 P000125 true
  proof PiBase.Formal.S10_P125
  provenance direct
  assumptions []

theorem S10_P175_not : ¬P175 PiBase.S10 := by
  intro h
  exact PiBase.SpaceConstructions.sierpinski_not_cardGeThree
    (P175.well_defined PiBase.S10_canonicalHomeomorph h)

register_certificate S000010 P000175 false
  proof PiBase.Formal.S10_P175_not
  provenance direct
  assumptions []

theorem S10_P196 : P196 PiBase.S10 :=
  P196.well_defined PiBase.S10_canonicalHomeomorph.symm
    (show PiBase.HereditarilyConnected PiBase.SpaceConstructions.Sierpinski from inferInstance)

register_certificate S000010 P000196 true
  proof PiBase.Formal.S10_P196
  provenance direct
  assumptions []

theorem S10_P201 : P201 PiBase.S10 :=
  P201.well_defined PiBase.S10_canonicalHomeomorph.symm
    (show PiBase.HasGenericPoint PiBase.SpaceConstructions.Sierpinski from inferInstance)

register_certificate S000010 P000201 true
  proof PiBase.Formal.S10_P201
  provenance direct
  assumptions []

theorem S10_P203 : P203 PiBase.S10 :=
  P203.well_defined PiBase.S10_canonicalHomeomorph.symm
    (show PiBase.AlmostDiscreteSpace PiBase.SpaceConstructions.Sierpinski from inferInstance)

register_certificate S000010 P000203 true
  proof PiBase.Formal.S10_P203
  provenance direct
  assumptions []

end PiBase.Formal

/- BEGIN PIBASE TRAIT DERIVATIONS -/
/- Traits for S10 (Sierpinski space).
Direct obligations are handwritten outside this generated region:
  S10_P125 : P125 PiBase.S10  (Has multiple points)
  S10_P175_not : ¬ P175 PiBase.S10  (Cardinality $\geq 3$)
  S10_P196 : P196 PiBase.S10  (Hereditarily connected)
  S10_P201 : P201 PiBase.S10  (Has a generic point)
  S10_P203 : P203 PiBase.S10  (Almost discrete)

Generated derived declarations:
-/

namespace PiBase.Formal

theorem S10_P176_not : ¬ P176 PiBase.S10 := by
  intro h
  exact S10_P175_not (T430 PiBase.S10 inferInstance h)

register_certificate S000010 P000176 false
  proof PiBase.Formal.S10_P176_not
  provenance derived
  assumptions []

theorem S10_P204_not : ¬ P204 PiBase.S10 := by
  intro h
  exact S10_P175_not (T558 PiBase.S10 inferInstance h)

register_certificate S000010 P000204 false
  proof PiBase.Formal.S10_P204_not
  provenance derived
  assumptions []

theorem S10_P126 : P126 PiBase.S10 :=
  T572 PiBase.S10 inferInstance S10_P203

register_certificate S000010 P000126 true
  proof PiBase.Formal.S10_P126
  provenance derived
  assumptions []

theorem S10_P51 : P51 PiBase.S10 :=
  T573 PiBase.S10 inferInstance S10_P203

register_certificate S000010 P000051 true
  proof PiBase.Formal.S10_P51
  provenance derived
  assumptions []

theorem S10_P205_not : ¬ P205 PiBase.S10 := by
  intro h
  exact S10_P204_not (T635 PiBase.S10 inferInstance h)

register_certificate S000010 P000205 false
  proof PiBase.Formal.S10_P205_not
  provenance derived
  assumptions []

theorem S10_P73 : P73 PiBase.S10 :=
  T865 PiBase.S10 inferInstance S10_P51

register_certificate S000010 P000073 true
  proof PiBase.Formal.S10_P73
  provenance derived
  assumptions []

theorem S10_P1 : P1 PiBase.S10 :=
  T143 PiBase.S10 inferInstance S10_P126

register_certificate S000010 P000001 true
  proof PiBase.Formal.S10_P1
  provenance derived
  assumptions []

theorem S10_P192 : P192 PiBase.S10 :=
  T511 PiBase.S10 inferInstance S10_P73

register_certificate S000010 P000192 true
  proof PiBase.Formal.S10_P192
  provenance derived
  assumptions []

end PiBase.Formal
/- END PIBASE TRAIT DERIVATIONS -/
