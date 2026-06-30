import Mathlib

#check Nat

inductive OrdNotation where
  | zero : OrdNotation
  | successor : OrdNotation → OrdNotation
  | limit : (Nat → OrdNotation) → OrdNotation
/-
Attempt is to taking the supremum of f(0),f(1),... So, take a sequence
of Ordinal Notations indexed by natural numbers and represent.
-/
open OrdNotation

-- Denote finite ordinals as the defined ordinal notations
def NatToOrd : Nat → OrdNotation
  | 0 => zero
  | n + 1 => successor (NatToOrd n)

def omega : OrdNotation :=
  limit NatToOrd


/-
We are proving linearity and well-foundedness of the semantic order
induced by the definition, not of the raw constructor syntax itself.
-/
noncomputable def toOrdinal : OrdNotation → Ordinal.{0}
  | zero => 0
  | successor a => toOrdinal a + 1
  | limit f => sSup (Set.range (fun n : Nat => toOrdinal (f n)))

noncomputable def le (a b : OrdNotation) : Prop :=
  toOrdinal a ≤ toOrdinal b

noncomputable def lt (a b : OrdNotation) : Prop :=
  toOrdinal a < toOrdinal b

theorem linear (a b : OrdNotation) : le a b ∨ le b a := by
  unfold le
  exact le_total (toOrdinal a) (toOrdinal b)

theorem lt_wf : WellFounded lt := by
  unfold lt
  exact InvImage.wf toOrdinal Ordinal.lt_wf

-- A raw `limit f` is only a genuine limit if the sequence is increasing.
def IsGenuineLimit : OrdNotation → Prop
  | limit f => ∀ n : Nat, lt (f n) (f (n + 1))
  | _ => False

#check IsGenuineLimit omega

/-
As of here, we can have 'zero = limit (fun _ → zero). le is not a true
linear ordering on raw notation.
-/
