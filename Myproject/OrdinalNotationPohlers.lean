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
To represent this, we define a constructor cnf : List OT → OT. cnf [] represents
zero.
-/
inductive OT where
  | cnf : List OT → OT

namespace OT
-- Define some introductory values
-- 0
def zero : OT := cnf []
-- 1 (ω^0)
def one : OT := cnf [zero]
-- 2 (ω^0 + ω^0)
def two : OT := cnf [zero, zero]
-- ω
def omegaOT := cnf [one]



-- COMPARISON
/-
To formalize our own ordinal notations, we define our own synctactic definition of comparison.
Pohler defines the comparison of ordinal terms by mapping each ordinal term to an ordinal
and using the comparison of ordinals. Here, we define the comparison of ordinal terms
lexiographically:
        Given a = cnf [a_1,...,a_n] and b = cnf [b_1,...,b_m], a < b iff
        (1) a_1 < b_1, or
        (2) a_1 = b_1 and a_2 < b_2, or
        ...
        (i) a_1 = b_1, ..., a_i-1 = b_i-1 and a_i < b_i
        ...
-/
mutual
inductive lt : OT → OT → Prop where
  | cnf_lt {xs ys : List OT} : lt_list xs ys → lt (cnf xs) (cnf ys)
inductive lt_list : List OT → List OT → Prop where
  | nil_cons {x : OT} {xs : List OT} : lt_list [] (x :: xs)
  | head_cons {x y : OT} {xs ys : List OT} : lt x y → lt_list (x :: xs) (y :: ys)
  | tail_cons {x : OT} {xs ys : List OT} : lt_list xs ys → lt_list (x :: xs) (x :: ys)
end
infix:50 " ≺ " => lt -- Denote lt as ≺
-- zero ≺ one
example : zero ≺ one := by
  unfold zero
  unfold one
  exact lt.cnf_lt (lt_list.nil_cons)
-- one ≺ two
example : one ≺ two := by
  unfold two one zero
  exact lt.cnf_lt (lt_list.tail_cons (lt_list.nil_cons))
-- one ≺ omegaOT
example : one ≺ omegaOT := by
  unfold omegaOT one zero
  exact lt.cnf_lt (lt_list.head_cons (lt.cnf_lt (lt_list.nil_cons)))

def leq (a b : OT) : Prop := a ≺ b ∨ a = b
infix:50 " ≼ " => leq



-- NORMALITY
/-
Cantor nomral forms < ε₀ must have their exponents decreasing
-/
mutual
inductive normal : OT → Prop where
  | cnf {xs : List OT} : normalList xs → normal (cnf xs)
inductive normalList : List OT → Prop where
  | nil : normalList []
  | singleton {x : OT} : normal x → normalList [x]
  | cons {x y : OT} {xs : List OT} : normal x → normalList (y :: xs) → y ≼ x
                                              → normalList (x :: y :: xs)
end
example : normal zero := by
  unfold zero
  exact normal.cnf (normalList.nil)
example : normal one := by
  unfold one zero
  exact normal.cnf (normalList.singleton (normal.cnf (normalList.nil)))
example : normal two := by
  unfold two zero
  exact normal.cnf
    (normalList.cons
      (normal.cnf normalList.nil)
      (normalList.singleton (normal.cnf normalList.nil))
      (by right; rfl))
example : normal omegaOT := by
  unfold omegaOT one zero
  exact normal.cnf
    (normalList.singleton
      (normal.cnf
        (normalList.singleton
          (normal.cnf normalList.nil))))



-- TRICHOTOMY / TOTALITY (LINEARTY)
/-
When we attempt to assign semantics to our ordinal notation, we must consider that they are
linearly ordered and well-founded. In doing so, we first show trichotomy of our defined universe,
that is,
              Given a,b : OT, either a ≺ b, a = b, or b ≺ a
We are omitting the normal condition as the cnf definition still satisfies trichotomy.
-/
-- Trichotomy
mutual
theorem lt_trichotomy : ∀ a b : OT, a ≺ b ∨ a = b ∨ b ≺ a
  | cnf xs, cnf ys => by
      have h := ltList_trichotomy xs ys -- lt_list xs ys ∨ xs = ys ∨ lt_list ys xs
      cases h with
      -- assume lt_list xs ys is true
      | inl hlt => left; exact lt.cnf_lt hlt
      -- assume ys ∨ xs = ys ∨ lt_list ys xs is true
      | inr h => cases h with
                 -- assume xs = ys is true
                 | inl heq => right; left; cases heq; rfl
                 -- assume lt_list ys xs is true
                 | inr hgt => right; right; exact lt.cnf_lt hgt
theorem ltList_trichotomy : ∀ xs ys : List OT, lt_list xs ys ∨ xs = ys ∨ lt_list ys xs
  | [], [] => by right; left; rfl
  | [], y :: ys => by left; exact lt_list.nil_cons
  | x :: xs, [] => by right; right; exact lt_list.nil_cons
  | x :: xs, y :: ys => by
      have hhead := lt_trichotomy x y
      cases hhead with
      -- case of x ≺ y is true
      | inl hxy => left; exact lt_list.head_cons hxy
      -- case of x = y ∨ y ≺ x is true
      | inr h => cases h with
          -- case of x = y
          | inl heq =>
              subst y
              have htail := ltList_trichotomy xs ys
              cases htail with
              -- lt_list xs ys
              | inl hxsys => left; exact lt_list.tail_cons hxsys
              -- xs = ys ∨ lt_list ys xs
              | inr h2 =>
                  cases h2 with
                  -- xs = ys
                  | inl hxsEq => subst ys; right; left; rfl
                  | inr hysxs => right; right; exact lt_list.tail_cons hysxs
          | inr hyx => right; right; exact lt_list.head_cons hyx
end
-- Totatlity
theorem lq_total (a b : OT) : a ≼ b ∨ b ≼ a := by
  have h := lt_trichotomy a b
  cases h with
  | inl hab => left; left; exact hab
  | inr rest => cases rest with
              | inl heq => left; right; exact heq
              | inr hba => right; left; exact hba



-- LINEAR ORDERING
/-
Linear ordering has a couple of conditions. One is linearity as we have just proven. We also must
prove irreflexivity, assymetry, and transitivity.
-/
-- Irreflexivity
mutual
theorem lt_irfl : ∀ a : OT, ¬ a ≺ a
  | cnf xs => by intro h
                 cases h with
                 | cnf_lt hlist => exact lt_list_irfl xs hlist
theorem lt_list_irfl : ∀ xs : List OT, ¬ lt_list xs xs
  | [] => by
          intro h
          cases h
  | x :: xs => by intro h
                  cases h with
                  | head_cons hxy => exact lt_irfl x hxy
                  | tail_cons htail => exact lt_list_irfl xs htail
end
-- Transitivity
mutual
theorem lt_trans : ∀ {a b c :OT}, a ≺ b → b ≺ c → a ≺ c
  | cnf xs, cnf ys, cnf zs, lt.cnf_lt hxy, lt.cnf_lt hyz => lt.cnf_lt (lt_list_trans hxy hyz)
theorem lt_list_trans : ∀ {xs ys zs : List OT}, lt_list xs ys → lt_list ys zs → lt_list xs zs
  | _, _, _, lt_list.nil_cons, hyz => by cases hyz with
                                        | head_cons h => exact lt_list.nil_cons
                                        | tail_cons h => exact lt_list.nil_cons
  | _, _, _, head_cons hxy, hyz => by cases hyz with
                                        | head_cons hyz => exact lt_list.head_cons (lt_trans hxy hyz)
                                        | tail_cons hyz => exact lt_list.head_cons hxy
  | _, _, _, .tail_cons hxy, hyz => by
      cases hyz with
      | head_cons hyz =>
          exact lt_list.head_cons hyz
      | tail_cons hyz =>
          exact lt_list.tail_cons (lt_list_trans hxy hyz)
end


end OT
