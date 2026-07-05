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
-- Transitive (leq)
theorem leq_trans {a b c : OT} : a ≼ b → b ≼ c → a ≼ c := by
  intro hab hbc
  cases hab with
    | inl hab_lt =>
        cases hbc with
          | inl hbc_lt =>
              left
              exact lt_trans hab_lt hbc_lt
          | inr hbc_eq =>
              left
              simpa [hbc_eq] using hab_lt
    | inr hab_eq =>
        cases hbc with
          | inl hbc_lt =>
              left
              simpa [← hab_eq] using hbc_lt
          | inr hbc_eq =>
              right
              exact Eq.trans hab_eq hbc_eq
lemma cnf_lt_of_lt_is_le {a b c : cnfOT} : a ≺ₙ b → b ≼ₙ c → a ≺ₙ c := by
  intro hab hbc
  cases hbc with
    | inl lt => exact cnf_lt_trans hab lt
    | inr eq => simpa [cnf_lt, eq] using hab
lemma cnf_lt_of_le_of_lt {a b c : cnfOT} : a ≼ₙ b → b ≺ₙ c → a ≺ₙ c := by
  intro hab hbc
  cases hab with
    | inl lt => exact cnf_lt_trans lt hbc
    | inr eq => simpa [cnf_lt, eq] using hbc

-- Reflective (leq)
lemma cnf_leq_refl (a : cnfOT) : a ≼ₙ a := by
  right; rfl

/-
This concludes the proof of linear ordering of cnfOT
-/


-- WELL_FOUNDEDNESS

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
-- Comparison of List of cnfOT
def cnfOTList_lt (xs ys : cnfOTList) : Prop := lt_list xs.1 ys.1

/-
Every element of a list is bouned by some term.
Mathematically, the exponents of the CNF have to be decreasing. Then, obviously, the all exponents
are bounded above by the first exponent.
-/
def listBoundedBy (x : OT) (xs : List OT) : Prop := ∀ y : OT, y ∈ xs → y ≼ x

/-
The elements of a normal list are all normal.
We have defined cnfOTList as a tuple. But this is, intuitively, trying to retrieve the reverse
direction.
-/
-- Head case
lemma normalList_head_normal {x : OT} {xs : List OT} : normalList (x :: xs) → normal x := by
  intro h
  cases xs with
    | nil => cases h with
              | singleton s => exact s
    | cons a as => cases h with
                    | cons hx htail hyx => exact hx
-- Tail case
lemma normalList_tail_normal {x : OT} {xs : List OT} : normalList (x :: xs) → normalList xs := by
  intro h
  cases xs with
    | nil => exact normalList.nil
    | cons a as => cases h with
                    | cons hx htail hyx => exact htail
lemma normalList_tail_bounded_by_head {x : OT} {xs : List OT} :
    normalList (x :: xs) → listBoundedBy x xs := by
  induction xs generalizing x with
    | nil =>
        intro h y hy
        cases hy
    | cons z zs ih =>
        intro h y hy
        cases h with
          | cons hx htail hzx =>
              simp at hy
              cases hy with
                | inl hy_eq =>
                    simpa [hy_eq] using hzx
                | inr hy_tail =>
                    have hy_le_z : y ≼ z := by
                      exact ih htail y hy_tail
                    exact leq_trans hy_le_z hzx
lemma normalList_bounded_by_head {x : OT} {xs : List OT} :
    normalList (x :: xs) → listBoundedBy x (x :: xs) := by
  intro h z hz
  simp at hz
  cases hz with
    -- z = x
    | inl hz_eq => subst z; right; rfl
    | inr hz_tail =>
        exact normalList_tail_bounded_by_head h z hz_tail
/-
Our goal is to prove accessibility of all cnfOT. Fixing arbitrary a : cnfOT, the definition is
∀ b ≺ₙ a, Acc cnf_lt b.
-/
lemma acc_of_lt {x y : cnfOT} (hx : Acc cnf_lt x) (hyx : y≺ₙx) : Acc cnf_lt y := by
  exact Acc.inv hx hyx
lemma acc_of_le {x y : cnfOT} (hx : Acc cnf_lt x) (hyx : y≼ₙx) : Acc cnf_lt y := by
  cases hyx with
    | inl hlt => exact Acc.inv hx hlt
    | inr heq =>
      have hxy : y = x := Subtype.ext heq
      simpa [hxy] using hx
/-
cnfOT [] is accessible
-/
lemma nil_list_acc : Acc cnfOTList_lt ⟨[], normalList.nil⟩ := by
  apply Acc.intro
  intro y hy
  rcases y with ⟨ys, ysNormal⟩
  unfold cnfOTList_lt at hy
  cases hy
/-
Suppose x : cnfOT bounds xs : cnfOTList. If x is accessible w.r.t. cnf_lt, then each of xs
is accessible.
-/
theorem boundedList_acc (x : cnfOT) (hx : Acc cnf_lt x) :
∀ xs : cnfOTList, listBoundedBy x.1 xs.1 → Acc cnfOTList_lt xs := by
  /-
  We are assuming that for all y ≺ₙ x that satisfies Acc cnf_lt y, the theorem statement holds.
  That is, ∀ xs : cnfOTList, listBoundedBy y.1 xs.1 → Acc cnfOTList_lt xs. In the code below,
            h : ∀ y ≺ₙ x, Acc cnf_lt y
            ih : ∀ xs : cnfOTList, listBoundedBy y.1 xs.1 → Acc cnfOTList_lt xs
  -/
  induction hx with
  -- Goal : ∀ xs : cnfOTList, listBoundedBy x.1 xs.1 → Acc cnfOTList_lt xs
    | intro x h ih =>
        intro xs hxs -- Fix arbitrary xs
                     -- Assume listBoundedBy x.1 xs.1 (hxs)
        -- Goal : Acc cnfOTList_lt xs
        rcases xs with ⟨xs, hxs_normal⟩
        revert hxs_normal hxs
        /- Goal : ∀ xs : cnfOTList, normalList xs → listBoundedBy x.1 xs.1 →
           Acc cnfOTList_lt ⟨xs, hxs_normal⟩ -/
        induction xs with
          | nil =>
              intro hxs_normal hxs
              -- Goal : Acc cnfOTList_lt ⟨[], hxs_normal⟩
              exact nil_list_acc
          /- IH : For any "cnfOTList_lt ys xs", assume
                  "normalList ys → listBoundedBy x.1 ys.1 → Acc cnfOTList_lt ⟨ys, hys_normal⟩"
             Goal : "∀ xs : cnfOTList, normalList xs → listBoundedBy x.1 xs.1 →
                     Acc cnfOTList_lt ⟨xs, hxs_normal⟩"
          -/
          | cons a as ihList =>
              intro hxs_normal hxs
              -- Goal : Acc cnfOTList_lt ⟨xs, hxs_normal⟩
              -- a is normal
              have ha_normal : normal a := by
                exact normalList_head_normal hxs_normal
              -- as is a normal list
              have has_normal : normalList as := by
                exact normalList_tail_normal hxs_normal
              -- a is less than x
              have ha_le_x : (⟨a, ha_normal⟩ : cnfOT) ≼ₙ x := by
                exact hxs a (by simp)
              -- x bounded elements of as from above
              have has_bound_by_x : listBoundedBy x.1 as := by
                intro y hy
                exact hxs y (by simp [hy])
              -- At this point, we know all elements of xs is less than x
              -- as is accessible
              have has_acc : Acc cnfOTList_lt ⟨as, has_normal⟩ := by
                exact ihList has_normal has_bound_by_x
              -- concatenating normal list ts with normal a gives accessible list
              have cons_acc_of_tail_acc : -- PROOF IS AI MUST CHECK
                  ∀ ts : cnfOTList,
                    Acc cnfOTList_lt ts →
                    ∀ hcons : normalList (a :: ts.1),
                      Acc cnfOTList_lt ⟨a :: ts.1, hcons⟩ := by
                intro ts hts_acc
                induction hts_acc with
                  | intro ts smaller ihTail =>
                      intro hcons
                      apply Acc.intro
                      intro ys hys
                      rcases ys with ⟨ys, hys_normal⟩
                      unfold cnfOTList_lt at hys
                      cases ys with
                        | nil =>
                            simpa using nil_list_acc
                        | cons b bs =>
                            cases hys with
                              | head_cons hb_lt_a =>
                                  have hb_normal : normal b := by
                                    exact normalList_head_normal hys_normal
                                  have hb_lt_a_n :
                                      (⟨b, hb_normal⟩ : cnfOT) ≺ₙ
                                      (⟨a, ha_normal⟩ : cnfOT) := by
                                    exact hb_lt_a
                                  have hb_lt_x :
                                      (⟨b, hb_normal⟩ : cnfOT) ≺ₙ x := by
                                    exact cnf_lt_of_lt_is_le hb_lt_a_n ha_le_x
                                  have hys_bound_by_b : listBoundedBy b (b :: bs) := by
                                    exact normalList_bounded_by_head hys_normal
                                  exact ih
                                    (⟨b, hb_normal⟩ : cnfOT)
                                    hb_lt_x
                                    ⟨b :: bs, hys_normal⟩
                                    hys_bound_by_b
                              | tail_cons hbs_lt_ts =>
                                  have hbs_normal : normalList bs := by
                                    exact normalList_tail_normal hys_normal
                                  have hbs_lt_ts' :
                                      cnfOTList_lt ⟨bs, hbs_normal⟩ ts := by
                                    unfold cnfOTList_lt
                                    exact hbs_lt_ts
                                  exact ihTail
                                    ⟨bs, hbs_normal⟩
                                    hbs_lt_ts'
                                    hys_normal
              exact cons_acc_of_tail_acc
                ⟨as, has_normal⟩
                has_acc
                hxs_normal

-- Convert a cnfOT into a cnf
def cnfList_as_cnfOT (xs : cnfOTList) : cnfOT := ⟨OT.cnf xs.1, normal.cnf xs.2⟩

/-
If xs is accessible w.r.t. cnfOTList_lt, then it is w.r.t. cnf_lt
-/
lemma cnf_acc_of_list_acc (xs : cnfOTList) (hxs_acc : Acc cnfOTList_lt xs) :
    Acc cnf_lt (cnfList_as_cnfOT xs) := by
  /-
  IH : ∀ ys, cnfOTList_lt ys xs → Acc cnfOTList_lt ys
  Goal : Acc cnf_lt (cnfList_as_cnfOT xs)
  -/
  induction hxs_acc with
    | intro xs hys ih =>
        rcases xs with ⟨xs, hxs_normal⟩
        apply Acc.intro
        /-
        Goal : ∀ b < cnfList_as_cnfOT xs, Acc cnf_lt z
        hb : cnf_lt b (cnfList_as_cnfOT xs)
        b : cnfOT
        -/
        intro b hb
        -- Goal : Acc cnf_lt z
        rcases b with ⟨b, hb_normal⟩
        -- b : OT, hb_normal : normal (cnf b)
        cases b with
          | cnf ys =>
              cases hb_normal with
                | cnf hys_normal =>
                    change OT.cnf ys ≺ OT.cnf xs at hb
                    cases hb with
                    | cnf_lt hlist =>
                        have hlist' :
                            cnfOTList_lt ⟨ys, hys_normal⟩ ⟨xs, hxs_normal⟩ := by
                          unfold cnfOTList_lt
                          exact hlist
                        simpa [cnfList_as_cnfOT] using ih ⟨ys, hys_normal⟩ hlist'
/-
Mutual accessibility. Every normal term/list is accessible.
-/
mutual
theorem cnfOT_acc : ∀ (a : OT) (ha : normal a), Acc cnf_lt ⟨a, ha⟩
  | OT.cnf as, normal.cnf nas => by
        simpa [cnfList_as_cnfOT] using cnf_acc_of_list_acc ⟨as, nas⟩ (cnfOTList_acc as nas)

theorem cnfOTList_acc : ∀ (xs : List OT) (hxs : normalList xs), Acc cnfOTList_lt ⟨xs, hxs⟩
  | [], normalList.nil => by
      exact nil_list_acc
  | [x], normalList.singleton hx => by
      have hx_acc : Acc cnf_lt (⟨x, hx⟩ : cnfOT) :=
        cnfOT_acc x hx
      exact boundedList_acc
        (⟨x, hx⟩ : cnfOT)
        hx_acc
        ⟨[x], normalList.singleton hx⟩
        (by
          intro y hy
          simp at hy
          subst y
          right
          rfl)
  | x :: y :: xs, normalList.cons hx htail hyx => by
      have hx_acc : Acc cnf_lt (⟨x, hx⟩ : cnfOT) :=
        cnfOT_acc x hx
      exact boundedList_acc
        (⟨x, hx⟩ : cnfOT)
        hx_acc
        ⟨x :: y :: xs, normalList.cons hx htail hyx⟩
        (normalList_bounded_by_head (normalList.cons hx htail hyx))
end

theorem cnf_lt_acc : ∀ a : cnfOT, Acc cnf_lt a := by
  intro a
  rcases a with ⟨a, ha⟩
  exact cnfOT_acc a ha

theorem cnf_lt_wf : WellFounded cnf_lt := by exact ⟨cnf_lt_acc⟩

end OT


/- Github push code
git status
git add .
git commit -m "update"
git push
-/
