import Mathlib
/-
We formalize the ordinal notations that correspond to ordinals below epsilon 0.
-/
-- ORDINAL TERMS
/-
Pohler defines |·|:OT → On by
(i) 0 ∈ OT with |0| = 0
(ii) a_1,...,a_n ∈ OT ∧ |a_1| ≥ ... ≥ |a_n| → <a_1,...,a_n> ∈ OT and
                                              |<a_1,...,a_n>|:=ω^|a_1|+...+ω^|a_n|
Instead of defining the constructer simply as List OT → OT, we do (OT → List OT) → OT.
This takes care of OT.cnf[] which repeats OT.zero. We will need a validity check for that.
The first OT term represents the
head of the OT list (a_1).
-/
inductive OT where
  | zero : OT
  | cnf : OT → List OT → OT

namespace OT
-- Define some introductory values
-- 1 (ω^0)
def one : OT := cnf zero []
-- 2 (ω^0 + ω^0)
def two : OT := cnf zero [zero]
-- ω
def omegaOT := cnf one []

-- COMPARISON
/-
To formalize our own ordinal notations, we define our own synctactic definition of comparison.
Pohler defines the comparison of ordinal terms by mapping each ordinal term to an ordinal
and using the comparison of ordinals. Here, we define the comparison of ordinal terms
lexiographically:
          a ≺ b iff (i) a = 0 and b ≠ 0
                    (ii) given a = a_head :: a_tail and b = b_head :: b_tail, a_head ≺ b_head
                    (iii) given a = h :: a_tail and b = h :: b_tail, a_tail ≺ b_tail
-/
mutual
inductive lt : OT → OT → Prop where
  | zero_cnf {a : OT} {ar : List OT}  : lt zero (cnf a ar)
  | head_cnf {a b : OT} {ar br : List OT} : lt a b → lt (cnf a ar) (cnf b br)
  | tail_cnf {a : OT} {ar br : List OT} : lt_list ar br → lt (cnf a ar) (cnf a br)
inductive lt_list : List OT → List OT → Prop where
  | nil_cons {a : OT} {ar: List OT} : lt_list [] (a :: ar)
  | cons_head {a b : OT} {ar br : List OT} : lt a b → lt_list (a :: ar) (b :: br)
  | cons_tail {a : OT} {ar br : List OT} : lt_list ar br → lt_list (a :: ar) (a :: br)
end
infix:50 " ≺ " => lt
-- 0 ≺ 1 (zero ≺ [zero])
example : zero ≺ one := by
  unfold one
  exact lt.zero_cnf
-- 1 ≺ 2 ([zero] ≺ [zero, zero])
example : one ≺ two := by
  unfold two
  unfold one
  exact lt.tail_cnf lt_list.nil_cons
-- 1 ≺ omegaOT ([zero] ≺ [one])
example : one ≺ omegaOT := by
  unfold omegaOT
  unfold one
  exact lt.head_cnf lt.zero_cnf

-- VALIDITY
/-
In out constructor, we allow forms of non CNFs. say we have
            ω^a_1 + ω^a_2 + ω^a_3 + ...
We must have a_1 ≥ a_2 ≥ a_3 ≥ .... We take care of that here.
-/
-- Less than or equal to
def le (o1 o2 : OT) : Prop :=
  lt o1 o2 ∨ o1 = o2
infix:50 " ≼ " => le
-- Valid OT and OT list
mutual
inductive validOT : OT → Prop where
  | zero : validOT zero
  | cnf {a : OT} {ar : List OT} : validOTList (a :: ar) → validOT (cnf a ar)
inductive validOTList : List OT → Prop where
  | nil : validOTList []
  | singleton {a : OT} : validOT a → validOTList [a]
  | cons {a b : OT} {ar : List OT} : validOT a → b ≼ a → validOTList (b :: ar)
                                                     → validOTList (a :: b :: ar)
end
-- 0 is valid
example : validOT zero := by
  exact validOT.zero
-- 1 is valid (1 ≃ cnf zero [] = [zero])
example : validOT one := by
  unfold one
  exact validOT.cnf (validOTList.singleton validOT.zero)
-- 2 is valid (2 = [zero, zero])
example : validOT two := by
  unfold two
  exact validOT.cnf (validOTList.cons (validOT.zero) (by
        right
        rfl)
        (validOTList.singleton validOT.zero))
-- omegaOT is valid (omegaOT = [one])
example : validOT omegaOT := by
  unfold omegaOT
  exact validOT.cnf
    (validOTList.singleton
      (by
        unfold one
        exact validOT.cnf (validOTList.singleton validOT.zero)))

-- TRICHOTOMY
/-
We want to recursively prove that trichotomy is satisfied by our defined comparison
relation. In doing so, we must assure the recursion ends and we do so by measuring the
complexity of an OT. By complexity, we mean, specifically, the number of constructors
involved.
-/
mutual
/-
We explain what we exactly we want to measure with the following examples.
ex1. one
one = cnf zero [] = [zero]. The number 0f constructors is simply 2, which are zero and [].
Applying the following definitions,
  sizeOT(one) = sizeOT(cnf zero []) = sizeOT(zero)+sizeOTList([])+1=2
ex2. two
two = cnf zero [zero] = zero :: zero :: []. So, it has four constructors (cnf, zero, ::, zero).
Plugging it in,
  sizeOT(two) = sizeOT(cnf zero [zero]) = sizeOT(zero) + sizeOTList(zero :: []) + 1
              = 1 + (sizeOT(zero) + sizeOTList([]) + 1) + 1
              = 4
ex3. omegaOT
omegaOT = cnf one [] = cnf (cnf zero []) [], so it must have three constructors. Checking,
  sizeOT(omegaOT) = sizeOT(one) + sizeOTList([]) + 1 = 3
-/
def sizeOT : OT → Nat
  | zero => 1
  | cnf a ar => sizeOT a + sizeOTList ar + 1
def sizeOTList : List OT → Nat
  | [] => 0
  | a :: ar => sizeOT a + sizeOTList ar + 1
end
#eval sizeOT (zero)
#eval sizeOT (one)
#eval sizeOT (two)
#eval sizeOT (omegaOT)

mutual

theorem lt_trichotomy : ∀ a b : OT, a ≺ b ∨ a = b ∨ b ≺ a
  | zero, zero => by right; left; rfl
  | zero, cnf b br => by left; exact lt.zero_cnf
  | cnf a ar, zero => by right; right; exact lt.zero_cnf
  | cnf a ar, cnf b br => by
      have h := lt_trichotomy a b
      cases h with
      | inl hab => left; exact lt.head_cnf hab
      | inr h =>
          cases h with
          | inl heq =>
              subst b
              have hlist := lt_list_trichotomy ar br
              cases hlist with
              | inl harbr => left; exact lt.tail_cnf harbr
              | inr h2 =>
                  cases h2 with
                  | inl heqList => subst br; right; left; rfl
                  | inr hbrar => right; right; exact lt.tail_cnf hbrar
          | inr hba => right; right; exact lt.head_cnf hba


theorem lt_list_trichotomy : ∀ xs ys : List OT, lt_list xs ys ∨ xs = ys ∨ lt_list ys xs
  | [], [] => by
      right
      left
      rfl

  | [], b :: br => by
      left
      exact lt_list.nil_cons

  | a :: ar, [] => by
      right
      right
      exact lt_list.nil_cons

  | a :: ar, b :: br => by
      have h := lt_trichotomy a b
      cases h with
      | inl hab =>
          left
          exact lt_list.cons_head hab

      | inr h =>
          cases h with
          | inl heq =>
              subst b
              have htail := lt_list_trichotomy ar br
              cases htail with
              | inl harbr =>
                  left
                  exact lt_list.cons_tail harbr

              | inr h2 =>
                  cases h2 with
                  | inl heqList =>
                      subst br
                      right
                      left
                      rfl

                  | inr hbrar =>
                      right
                      right
                      exact lt_list.cons_tail hbrar

          | inr hba =>
              right
              right
              exact lt_list.cons_head hba

end

end OT



/-
git status
git add .
git commit -m "New"
git push
-/
