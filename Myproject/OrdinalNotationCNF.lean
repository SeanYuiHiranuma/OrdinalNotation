import Mathlib

/-
We failed to include the canonical ordering of ordinal notations in the
previous file when we defined the limit ordinal as the value associated
with a sequence of mappings from ℕ. Here, we attempt to defined them in
Cantor Noraml Form
-/

inductive CNF where
  | zero : CNF
  | cons : CNF → CNF → CNF
open CNF
/-
zero to make it to mean 0
cons a b to make it to mean ω^a+b
we want the exponents to be in decreasing order
-/

def one : CNF := cons zero zero --0
def two : CNF := cons zero one --1+1
def omegaCNF :CNF := cons one zero --ω+0

namespace CNF

/-
lt CNF1 CNF2 to mean CNF1 is less than CNF2

We want ω^a + b < ω^c + d iff
either a < c or a = c and b < d
-/
def lt (c1 c2 : CNF) : Prop :=
  match c1, c2 with
  | zero, zero => False
  | zero, cons _ _ => True
  | cons _ _, zero => False
  | cons a b, cons c d =>
    lt a c ∨ (a = c ∧ lt b d)
-- Test 0<1
example : lt zero one := by
  unfold one
  simp [lt]
--Test 1<2
example : lt one two := by
  unfold two
  unfold one
  simp [lt]
--Test 2<ω
example : lt two omegaCNF := by
  unfold two
  unfold omegaCNF
  unfold one
  simp [lt]


def le (c1 c2 : CNF) : Prop :=
  c1 = c2 ∨ lt c1 c2
/-
We next want to assure that the leading exponent of b in ω^a+b is ≤ a
-/
def leadingExpLe (b a : CNF) : Prop :=
  match b with
  | zero => True
  | cons c _ => le c a

/-
Having all the ingredients needed, we ensure if something is indeed
Cantor Normal Form
-/
def isNormal (c : CNF) : Prop :=
  match c with
    | zero => True
    | cons a b => isNormal a ∧ isNormal b ∧ leadingExpLe b a
-- zero is normal
example : isNormal zero := by
  simp [isNormal]
-- one is normal
example : isNormal one := by
  unfold one
  simp [isNormal, leadingExpLe]
-- two is normal
example : isNormal two := by
   simp [two, one, isNormal, leadingExpLe, le, lt]
-- omega = ω^1 is normal
example : isNormal omegaCNF := by
  simp [omegaCNF, one, isNormal, leadingExpLe]

/-
Now we want to prove that given any CNF a and b, a<b, a=b, or b<a
-/
theorem threeWayComparison (a b : CNF) : lt a b ∨ a = b ∨ lt b a := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => right; left; rfl
      | cons c d => left; simp [lt]
  | cons a1 a2 ih1 ih2 =>
      cases b with
      | zero => right; right; simp [lt]
      | cons b1 b2 =>
          have hExp := ih1 b1
          rcases hExp with hExpLt | hExpRest
          · left
            simp [lt, hExpLt]
          · rcases hExpRest with hExpEq | hExpGt
            · have hTail := ih2 b2
              rcases hTail with hTailLt | hTailRest
              · left
                simp [lt, hExpEq, hTailLt]
              · rcases hTailRest with hTailEq | hTailGt
                · right
                  left
                  rw [hExpEq, hTailEq]
                · right
                  right
                  simp [lt, hExpEq, hTailGt]
            · right
              right
              simp [lt, hExpGt]

/-
Now we know that CNF is linear (complete? i forgot the name of it),
we want to show it is linearly ordered. That is, irreflexive, asymmetric,
and transitive.
-/
-- 1. Irreflexivity
theorem ltIrrefl (a : CNF) : ¬ lt a a := by
  induction a with
  | zero => simp [lt]
  | cons a1 a2 ih1 ih2 =>
      intro h; simp [lt] at h
      rcases h with hExp | hTail
      · exact ih1 hExp
      · exact ih2 hTail

-- 2. Transitivity
theorem ltTrans (a b c : CNF) : lt a b → lt b c → lt a c := by
  induction a generalizing b c with
  | zero =>
      intro hab hbc
      cases b with
      | zero =>
          simp [lt] at hab
      | cons b1 b2 =>
          cases c with
          | zero =>
              simp [lt] at hbc
          | cons c1 c2 =>
              simp [lt]
  | cons a1 a2 ih1 ih2 =>
      intro hab hbc
      cases b with
      | zero =>
          simp [lt] at hab
      | cons b1 b2 =>
          cases c with
          | zero =>
              simp [lt] at hbc
          | cons c1 c2 =>
              simp [lt] at hab; simp [lt] at hbc; simp [lt]
              rcases hab with hExpAB | hTailAB
              · rcases hbc with hExpBC | hTailBC
                · left
                  exact ih1 b1 c1 hExpAB hExpBC
                · rcases hTailBC with ⟨hEqBC, hTailBC_lt⟩
                  left
                  rw [← hEqBC]
                  exact hExpAB
              · rcases hTailAB with ⟨hEqAB, hTailAB_lt⟩
                rcases hbc with hExpBC | hTailBC
                · left
                  rw [hEqAB]
                  exact hExpBC
                · rcases hTailBC with ⟨hEqBC, hTailBC_lt⟩
                  right
                  constructor
                  · exact hEqAB.trans hEqBC
                  · exact ih2 b2 c2 hTailAB_lt hTailBC_lt

-- 3. Assymetry
theorem ltAsymm (a b : CNF) : lt a b → ¬ lt b a := by
  intro hab hba
  have h : lt a a := ltTrans a b a hab hba
  exact ltIrrefl a h

-- 4. Linearity of ≤
theorem linear (a b : CNF) : le a b ∨ le b a := by
  have h := threeWayComparison a b
  rcases h with hlt | hRest
  · left; right; exact hlt
  · rcases hRest with heq | hgt
    · left; left; exact heq
    · right; right; exact hgt

-- 5. Antisymmetry of ≤
theorem leAntisymm (a b : CNF) : le a b → le b a → a = b := by
  intro hab hba
  rcases hab with heqAB | hltAB
  · exact heqAB
  · rcases hba with heqBA | hltBA
    · exact heqBA.symm
    · exfalso
      exact ltAsymm a b hltAB hltBA

/-
Next is well foundedness
-/


end CNF
