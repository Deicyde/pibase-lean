module

public import PiBaseLean.Properties.P52.Defs
public import PiBaseLean.Spaces.Constructions.Finite.Lemmas
public import PiBaseLean.Spaces.S1.Defs

-- BEGIN PIBASE TRAIT IMPORTS
public meta import PiBaseLean.Audit.Spaces.Registry
public import PiBaseLean.Properties.P1.Defs
public import PiBaseLean.Properties.P2.Defs
public import PiBaseLean.Properties.P3.Defs
public import PiBaseLean.Properties.P4.Defs
public import PiBaseLean.Properties.P5.Defs
public import PiBaseLean.Properties.P6.Defs
public import PiBaseLean.Properties.P7.Defs
public import PiBaseLean.Properties.P8.Defs
public import PiBaseLean.Properties.P11.Defs
public import PiBaseLean.Properties.P12.Defs
public import PiBaseLean.Properties.P13.Defs
public import PiBaseLean.Properties.P14.Defs
public import PiBaseLean.Properties.P15.Defs
public import PiBaseLean.Properties.P53.Defs
public import PiBaseLean.Properties.P55.Defs
public import PiBaseLean.Properties.P67.Defs
public import PiBaseLean.Properties.P84.Defs
public import PiBaseLean.Properties.P86.Defs
public import PiBaseLean.Properties.P112.Defs
public import PiBaseLean.Properties.P121.Defs
public import PiBaseLean.Properties.P126.Defs
public import PiBaseLean.Properties.P132.Defs
public import PiBaseLean.Properties.P134.Defs
public import PiBaseLean.Properties.P135.Defs
public import PiBaseLean.Properties.P165.Defs
public import PiBaseLean.Properties.P176.Defs
public import PiBaseLean.Properties.P191.Defs
public import PiBaseLean.Properties.P192.Defs
public import PiBaseLean.Properties.P204.Defs
public import PiBaseLean.Properties.P205.Defs
public import PiBaseLean.Properties.P219.Defs
public import PiBaseLean.Theorems.T33.Theorem
public import PiBaseLean.Theorems.T36.Theorem
public import PiBaseLean.Theorems.T37.Theorem
public import PiBaseLean.Theorems.T42.Theorem
public import PiBaseLean.Theorems.T77.Theorem
public import PiBaseLean.Theorems.T85.Theorem
public import PiBaseLean.Theorems.T99.Theorem
public import PiBaseLean.Theorems.T113.Theorem
public import PiBaseLean.Theorems.T115.Theorem
public import PiBaseLean.Theorems.T119.Theorem
public import PiBaseLean.Theorems.T144.Theorem
public import PiBaseLean.Theorems.T146.Theorem
public import PiBaseLean.Theorems.T153.Theorem
public import PiBaseLean.Theorems.T154.Theorem
public import PiBaseLean.Theorems.T156.Theorem
public import PiBaseLean.Theorems.T193.Theorem
public import PiBaseLean.Theorems.T204.Theorem
public import PiBaseLean.Theorems.T256.Theorem
public import PiBaseLean.Theorems.T264.Theorem
public import PiBaseLean.Theorems.T268.Theorem
public import PiBaseLean.Theorems.T282.Theorem
public import PiBaseLean.Theorems.T283.Theorem
public import PiBaseLean.Theorems.T287.Theorem
public import PiBaseLean.Theorems.T401.Theorem
public import PiBaseLean.Theorems.T407.Theorem
public import PiBaseLean.Theorems.T430.Theorem
public import PiBaseLean.Theorems.T502.Theorem
public import PiBaseLean.Theorems.T519.Theorem
public import PiBaseLean.Theorems.T558.Theorem
public import PiBaseLean.Theorems.T635.Theorem
public import PiBaseLean.Theorems.T817.Theorem
-- END PIBASE TRAIT IMPORTS

@[expose] public section

namespace PiBase.Formal

/-! ## Direct catalog traits -/

theorem S1_P52 : P52 PiBase.S1 := by
  change DiscreteTopology PiBase.S1
  infer_instance

register_certificate S000001 P000052 true
  proof PiBase.Formal.S1_P52
  provenance direct
  assumptions []

theorem S1_P125 : P125 PiBase.S1 :=
  P125.well_defined PiBase.S1_canonicalHomeomorph.symm
    (show Nontrivial (PiBase.SpaceConstructions.FiniteDiscrete 2) from inferInstance)

register_certificate S000001 P000125 true
  proof PiBase.Formal.S1_P125
  provenance direct
  assumptions []

theorem S1_P175_not : ¬P175 PiBase.S1 := by
  intro h
  exact PiBase.SpaceConstructions.finiteDiscreteTwo_not_cardGeThree
    (P175.well_defined PiBase.S1_canonicalHomeomorph h)

register_certificate S000001 P000175 false
  proof PiBase.Formal.S1_P175_not
  provenance direct
  assumptions []

end PiBase.Formal

/- BEGIN PIBASE TRAIT DERIVATIONS -/
/- Traits for S1 (Discrete topology on $\{0,1\}$).
Direct obligations are handwritten outside this generated region:
  S1_P52 : P52 PiBase.S1  (Discrete)
  S1_P125 : P125 PiBase.S1  (Has multiple points)
  S1_P175_not : ¬ P175 PiBase.S1  (Cardinality $\geq 3$)

Generated derived declarations:
-/

namespace PiBase.Formal

theorem S1_P2 : P2 PiBase.S1 :=
  T42 PiBase.S1 inferInstance S1_P52

register_certificate S000001 P000002 true
  proof PiBase.Formal.S1_P2
  provenance derived
  assumptions []

theorem S1_P55 : P55 PiBase.S1 :=
  T85 PiBase.S1 inferInstance S1_P52

register_certificate S000001 P000055 true
  proof PiBase.Formal.S1_P55
  provenance derived
  assumptions []

theorem S1_P1 : P1 PiBase.S1 :=
  T119 PiBase.S1 inferInstance S1_P2

register_certificate S000001 P000001 true
  proof PiBase.Formal.S1_P1
  provenance derived
  assumptions []

theorem S1_P126 : P126 PiBase.S1 :=
  T144 PiBase.S1 inferInstance S1_P52

register_certificate S000001 P000126 true
  proof PiBase.Formal.S1_P126
  provenance derived
  assumptions []

theorem S1_P86 : P86 PiBase.S1 :=
  T204 PiBase.S1 inferInstance S1_P52

register_certificate S000001 P000086 true
  proof PiBase.Formal.S1_P86
  provenance derived
  assumptions []

theorem S1_P135 : P135 PiBase.S1 :=
  T287 PiBase.S1 inferInstance S1_P2

register_certificate S000001 P000135 true
  proof PiBase.Formal.S1_P135
  provenance derived
  assumptions []

theorem S1_P176_not : ¬ P176 PiBase.S1 := by
  intro h
  exact S1_P175_not (T430 PiBase.S1 inferInstance h)

register_certificate S000001 P000176 false
  proof PiBase.Formal.S1_P176_not
  provenance derived
  assumptions []

theorem S1_P204_not : ¬ P204 PiBase.S1 := by
  intro h
  exact S1_P175_not (T558 PiBase.S1 inferInstance h)

register_certificate S000001 P000204 false
  proof PiBase.Formal.S1_P204_not
  provenance derived
  assumptions []

theorem S1_P205_not : ¬ P205 PiBase.S1 := by
  intro h
  exact S1_P204_not (T635 PiBase.S1 inferInstance h)

register_certificate S000001 P000205 false
  proof PiBase.Formal.S1_P205_not
  provenance derived
  assumptions []

theorem S1_P219 : P219 PiBase.S1 :=
  T817 PiBase.S1 inferInstance S1_P52

register_certificate S000001 P000219 true
  proof PiBase.Formal.S1_P219
  provenance derived
  assumptions []

theorem S1_P53 : P53 PiBase.S1 :=
  T77 PiBase.S1 inferInstance S1_P55

register_certificate S000001 P000053 true
  proof PiBase.Formal.S1_P53
  provenance derived
  assumptions []

theorem S1_P121 : P121 PiBase.S1 :=
  T264 PiBase.S1 inferInstance S1_P53

register_certificate S000001 P000121 true
  proof PiBase.Formal.S1_P121
  provenance derived
  assumptions []

theorem S1_P15 : P15 PiBase.S1 :=
  T268 PiBase.S1 inferInstance S1_P121

register_certificate S000001 P000015 true
  proof PiBase.Formal.S1_P15
  provenance derived
  assumptions []

theorem S1_P112 : P112 PiBase.S1 :=
  T407 PiBase.S1 inferInstance S1_P53

register_certificate S000001 P000112 true
  proof PiBase.Formal.S1_P112
  provenance derived
  assumptions []

theorem S1_P67 : P67 PiBase.S1 :=
  T153 PiBase.S1 inferInstance ⟨S1_P2, S1_P15⟩

register_certificate S000001 P000067 true
  proof PiBase.Formal.S1_P67
  provenance derived
  assumptions []

theorem S1_P8 : P8 PiBase.S1 :=
  T154 PiBase.S1 inferInstance S1_P67

register_certificate S000001 P000008 true
  proof PiBase.Formal.S1_P8
  provenance derived
  assumptions []

theorem S1_P14 : P14 PiBase.S1 :=
  T156 PiBase.S1 inferInstance S1_P15

register_certificate S000001 P000014 true
  proof PiBase.Formal.S1_P14
  provenance derived
  assumptions []

theorem S1_P132 : P132 PiBase.S1 :=
  T256 PiBase.S1 inferInstance S1_P15

register_certificate S000001 P000132 true
  proof PiBase.Formal.S1_P132
  provenance derived
  assumptions []

theorem S1_P191 : P191 PiBase.S1 :=
  T502 PiBase.S1 inferInstance ⟨S1_P132, S1_P2⟩

register_certificate S000001 P000191 true
  proof PiBase.Formal.S1_P191
  provenance derived
  assumptions []

theorem S1_P13 : P13 PiBase.S1 :=
  T36 PiBase.S1 inferInstance S1_P14

register_certificate S000001 P000013 true
  proof PiBase.Formal.S1_P13
  provenance derived
  assumptions []

theorem S1_P12 : P12 PiBase.S1 :=
  T37 PiBase.S1 inferInstance ⟨S1_P13, S1_P135⟩

register_certificate S000001 P000012 true
  proof PiBase.Formal.S1_P12
  provenance derived
  assumptions []

theorem S1_P7 : P7 PiBase.S1 :=
  T99 PiBase.S1 inferInstance ⟨S1_P2, S1_P13⟩

register_certificate S000001 P000007 true
  proof PiBase.Formal.S1_P7
  provenance derived
  assumptions []

theorem S1_P6 : P6 PiBase.S1 :=
  T113 PiBase.S1 inferInstance S1_P7

register_certificate S000001 P000006 true
  proof PiBase.Formal.S1_P6
  provenance derived
  assumptions []

theorem S1_P5 : P5 PiBase.S1 :=
  T115 PiBase.S1 inferInstance S1_P6

register_certificate S000001 P000005 true
  proof PiBase.Formal.S1_P5
  provenance derived
  assumptions []

theorem S1_P11 : P11 PiBase.S1 :=
  T146 PiBase.S1 inferInstance S1_P5

register_certificate S000001 P000011 true
  proof PiBase.Formal.S1_P11
  provenance derived
  assumptions []

theorem S1_P134 : P134 PiBase.S1 :=
  T282 PiBase.S1 inferInstance S1_P11

register_certificate S000001 P000134 true
  proof PiBase.Formal.S1_P134
  provenance derived
  assumptions []

theorem S1_P3 : P3 PiBase.S1 :=
  T283 PiBase.S1 inferInstance ⟨S1_P134, S1_P1⟩

register_certificate S000001 P000003 true
  proof PiBase.Formal.S1_P3
  provenance derived
  assumptions []

theorem S1_P165 : P165 PiBase.S1 :=
  T401 PiBase.S1 inferInstance S1_P13

register_certificate S000001 P000165 true
  proof PiBase.Formal.S1_P165
  provenance derived
  assumptions []

theorem S1_P192 : P192 PiBase.S1 :=
  T519 PiBase.S1 inferInstance S1_P134

register_certificate S000001 P000192 true
  proof PiBase.Formal.S1_P192
  provenance derived
  assumptions []

theorem S1_P4 : P4 PiBase.S1 :=
  T33 PiBase.S1 inferInstance S1_P5

register_certificate S000001 P000004 true
  proof PiBase.Formal.S1_P4
  provenance derived
  assumptions []

theorem S1_P84 : P84 PiBase.S1 :=
  T193 PiBase.S1 inferInstance S1_P3

register_certificate S000001 P000084 true
  proof PiBase.Formal.S1_P84
  provenance derived
  assumptions []

end PiBase.Formal
/- END PIBASE TRAIT DERIVATIONS -/
