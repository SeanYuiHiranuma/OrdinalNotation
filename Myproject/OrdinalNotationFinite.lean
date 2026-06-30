import Mathlib

#check Nat

inductive OrdNotation where
  | zero : OrdNotation
  | successor : OrdNotation → OrdNotation
-- Limit is

-- Covert ordinal notation into Nat to prep order
def OrdNotationNat : OrdNotation → Nat
  | OrdNotation.zero => 0
  | OrdNotation.successor a => OrdNotationNat a + 1
#eval OrdNotationNat OrdNotation.zero
#eval OrdNotationNat (OrdNotation.successor (OrdNotation.successor (OrdNotation.zero)))

-- Define ordering (less than equal)
def OrdNotation.le (o1 o2 : OrdNotation) : Prop :=
 OrdNotationNat o1 ≤ OrdNotationNat o2
#check OrdNotation.le (OrdNotation.zero) (OrdNotation.successor (OrdNotation.zero))

-- Define ordering (less)
def OrdNotation.lt (o1 o2 : OrdNotation) : Prop :=
 OrdNotationNat o1 < OrdNotationNat o2

-- Linearity
theorem OrdNotation.linear (o1 o2 : OrdNotation) :
    OrdNotation.le o1 o2 ∨ OrdNotation.le o2 o1 := by
  unfold OrdNotation.le
  exact Nat.le_total (OrdNotationNat o1) (OrdNotationNat o2)

#check WellFounded
#check Nat.lt_wfRel
#check WellFoundedRelation

-- Well-Founded
theorem OrdNotation.lt_wf : WellFounded OrdNotation.lt := by
  unfold OrdNotation.lt
  exact InvImage.wf OrdNotationNat Nat.lt_wfRel.wf
