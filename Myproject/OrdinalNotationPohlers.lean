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
theorem leq_total (a b : OT) : a ≼ b ∨ b ≼ a := by
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
  | _, _, _, lt.cnf_lt hxy, lt.cnf_lt hyz => lt.cnf_lt (lt_list_trans hxy hyz)
theorem lt_list_trans : ∀ {xs ys zs : List OT}, lt_list xs ys → lt_list ys zs → lt_list xs zs
  | _, _, _, lt_list.nil_cons, hyz => by cases hyz with
                                      | head_cons h => exact lt_list.nil_cons
                                      | tail_cons h => exact lt_list.nil_cons
  | _, _, _, lt_list.head_cons hxy, hyz => by cases hyz with
                                      | head_cons hyz => exact lt_list.head_cons (lt_trans hxy hyz)
                                      | tail_cons hyz => exact lt_list.head_cons hxy
  | _, _, _, lt_list.tail_cons hxy, hyz => by
      cases hyz with
      | head_cons hyz =>
          exact lt_list.head_cons hyz
      | tail_cons hyz =>
          exact lt_list.tail_cons (lt_list_trans hxy hyz)
end
-- Asymmetry
theorem lt_asym {a b : OT} (hab : a ≺ b) : ¬ b ≺ a := by
  intro hba
  exact lt_irfl a (lt_trans hab hba)
-- Antisymmetry
theorem leq_antisym {a b : OT} (hab : a ≼ b) (hba : b ≼ a) : a = b := by
  cases hab with
    | inl hlt => cases hba with
                  | inl hgt => exact False.elim (lt_irfl a (lt_trans hlt hgt))
                  | inr heq => exact heq.symm
    | inr heq => exact heq
/-
This concludes the proof of linear ordering of OT
-/



-- CANTOR NORMAL FORM
/-
As of now, the defined cnf representation includes the case where the exponents are not
necessarily in decreasing order. We formalize that here. We also tweak the previous
definitions and theorems to the case specific to cnf.
-/
def cnfOT : Type := {a : OT // normal a}

-- Comparison
def cnf_lt (a b : cnfOT) : Prop := a.1 ≺ b.1
infix:50 "≺ₙ" => cnf_lt
def cnf_leq (a b : cnfOT) : Prop := a.1 ≼ b.1
infix:50 "≼ₙ" => cnf_leq

-- Trichotomy
theorem cnf_lt_trichotomy (a b : cnfOT) : a ≺ₙ b ∨ a = b ∨ b ≺ₙ a := by
  have h := lt_trichotomy a.1 b.1
  cases h with
    -- Assume a.1 ≺ b.1 it true
    | inl hab => left; exact hab
    -- Assume a.1 = b.1 ∨ b.1 ≺ a.1 is true
    | inr h => cases h with
                | inl heq => right; left; cases a; cases b; simp at heq; simp [heq]
                | inr hba => right; right; exact hba

-- Total
theorem cnf_leq_total (a b : cnfOT) : a ≼ₙ b ∨ b ≼ₙ a := by
  have h := cnf_lt_trichotomy a b
  cases h with
    | inl hab => left; left; exact hab
    | inr hba => cases hba with
                  | inl h1 => left; right; exact congrArg Subtype.val h1
                  | inr h2 => right; left; exact h2

-- Irreflexive
theorem cnf_lt_irfl (a : cnfOT) : ¬ a ≺ₙ a := by
  intro h
  exact lt_irfl a.1 h
-- Transitive
theorem cnf_lt_trans {a b c : cnfOT} : a ≺ₙ b → b ≺ₙ c → a ≺ₙ c := by
  intro hab hbc
  exact lt_trans hab hbc
-- Asymmetry
theorem cnf_lt_asym {a b : cnfOT} (hab : a≺ₙb) : ¬ b ≺ₙ a := by
  intro h
  exact lt_asym hab h
-- Antisymmetry
theorem cnf_leq_antisym {a b : cnfOT} (hab : a≼ₙb) (hba : b≼ₙa) : a = b := by
  apply Subtype.ext
  exact leq_antisym hab hba
/-
This concludes the proof of linear ordering of cnfOT
-/


-- WELL_FOUNDEDNESS
#check Acc
#check Acc.intro
#check WellFounded

/-
LEAN formalizes the concept of Well-Foundedness with the use of accessibility. "Acc lt a" will mean
every b below a is accessible. Intuitively, this will mean there are no infinite descending chain
starting from b. Induction seems to be the natural tool to prove this but the problem is limit
ordinals where we cannot define an immediate successor (ex. ω). Specifically, the structural
induction LEAN provides runs into a problem. For example, omegaOT has subterms one and zero. but
four has zero, zero, zero, zero which is structurally more complex but should still be "below"
omegaOT. This contradiction can be solve by the use of list_lt which lines up the OTs lexico-
graphically.
-/
-- List of cnfOT
def cnfOTList : Type := {xs : List OT // normalList xs}
def cnfOTList_lt (xs ys : cnfOTList) : Prop := lt_list xs.1 ys.1
/-
We want to prove that given any a : cnfOT, a is accessible with respect to ≼ₙ. That is, every
b ≼ₙ a is accessible. b ≼ₙ a means b.1 ≼ a.1, which is
                  cnf (some OT list for b) ≼ cnf (some OT list for a)
This relation, recall, is defined lexicographically, syntactically. This will mean, if
a is accessible, then every normal list whose elemetns are ≤ a is accessible. I emphasize
we consider the normal case and not the general OT.
-/
-- cnfList []
theorem cnfList_nil_acc : Acc cnfOTList_lt ⟨[], normalList.nil⟩ := by
  apply Acc.intro --change goal to ∀ b, cnfList_lt b ⟨[], normalList.nil⟩, Acc cnfList_lt b
  intro b hb
  unfold cnfOTList_lt at hb -- lt_list b.1 []
  rcases b with ⟨xs, hxs⟩
  cases hb
/-
So, when we focus on the list elements, as previously explained, a normal CNF lists are
decreasing. So, if the head element is accessible, the following should all be. We formalize that
here, but a more general case. That is, given accessible cnfOT x, all ≼ₙ x are accessible.
-/
def listBoundedBy (x : OT) (xs : List OT) : Prop := ∀ y, y ∈ xs → y ≼ x

/-
If an upperbound is accessible then it is accessible
-/
theorem bounded_acc (x y : cnfOT) (hyx : y≼ₙx) (hx : Acc cnf_lt x) : Acc cnf_lt y := by
  cases hyx with
    | inl hyx_lt => cases hx with
                      | intro x ih => exact ih y hyx_lt
    | inr hyx_eq => have hEq : y = x := Subtype.ext hyx_eq
                    simpa [hEq] using hx

theorem boundedList_acc (x : cnfOT) (hx : Acc cnf_lt x) (xs : cnfOTList)
                  (hxs : listBoundedBy x.1 xs.1) : Acc cnfOTList_lt xs := by
  induction hx generalizing xs with
    /-
    Induction, to prove the case for x, we assume the theorem holds for all y≺ₙx. Formally,
      "∀ y : cnfOT, cnf_lt y x → ∀ xs :cnfOTList, listBoundedBy y.1 xs.1 → Acc cnfOTList_lt xs"
    In the following LEAN format, x is in question, and ih is simply induction hypothesis. We
    prove Acc cnfOTList_lt xs, i.e., xs is accessible with respect to cnfOTList_lt
    -/
    | intro x ih => rcases xs with ⟨xs, hxss⟩ -- The list is the first coodinate
                    cases xs with -- Let xs denote the cnfOTList now
                    -- The goal is Acc cnfOTList_lt <[], hxs>
                    | nil => exact cnfList_nil_acc
                    /-
                    The goal is Acc cnfOTList_lt <a :: as, hxs>, where a : OT, as : OTList.
                    We can simply prove
                      "∀ ys : cnfOTList, cnfOTList_lt ys xs → Acc cnfOTList_lt ys"
                    "hys_lt" to stand for cnfOTList_lt ys xs
                    -/
                    | cons a as => apply Acc.intro
                                   intro ys hys_lt
                                   unfold cnfOTList_lt at hys_lt -- lt_list ys.1 xs.1
                                   rcases ys with ⟨ys, hysNorm⟩
                                   cases ys with
                                   | nil => exact cnfList_nil_acc
                                   | cons b bs => cases hys_lt with
                                                  /-
                                                  For this case, we have ys ≺ₙₗ xs because of
                                                  b ≺ₙ a, head comparison.
                                                  -/
                                                  | head_cons => sorry
                                                  | tail_cons => sorry


theorem cnf_lt_acc : ∀ a : cnfOT, Acc cnf_lt a := by sorry

theorem cnf_lt_wf : WellFounded cnf_lt := by exact ⟨cnf_lt_acc⟩

end OT


/- Github push code
git status
git add .
git commit -m "New definition; wf set-up"
git push
-/
