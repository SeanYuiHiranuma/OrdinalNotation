import Mathlib

--===============================================================================
-- Definition
--===============================================================================
/-
We follow Fernandez-Duque and Weiermann's notations. We represent the parameterized
collapsing function θ_X(ζ) as ψ(ζ) := θ_P(ζ) where P = {ω^{α} : α ∈ On}, the class
of principal ordinals.
-/
mutual
inductive countableOrd where
  | sum : List principal → countableOrd
inductive principal where
  | psi : omegaTerm → principal
-- ζ = Ω^{α}β + γ
inductive omegaTerm where
  | zero : omegaTerm
  -- In the order of α → β (0 < β < Ω) → γ
  | omegaNF : omegaTerm → countableOrd → omegaTerm → omegaTerm
end


--===============================================================================
-- Preliminaries
--===============================================================================
namespace countableOrd
def zero : countableOrd := sum []
def ofPrincipal (p : principal) : countableOrd := sum [p]
end countableOrd

namespace principal
def one : principal := psi omegaTerm.zero
end principal

namespace countableOrd
def one : countableOrd := ofPrincipal principal.one
def two : countableOrd := sum [principal.one, principal.one]
end countableOrd

namespace omegaTerm
-- Every countable ordinal β < Ω can be represented as Ω^{0}β+0
def ofCountable : countableOrd → omegaTerm
  | .sum [] => zero
  | .sum (p :: ps) => omegaNF zero (.sum (p :: ps)) zero
def one : omegaTerm := ofCountable (countableOrd.one)
def bigOmega : omegaTerm := omegaNF one countableOrd.one zero
def coefficients : omegaTerm → List countableOrd
  | zero => [countableOrd.zero]
  | omegaNF alpha beta gamma => (coefficients alpha) ++ (coefficients gamma) ++ [beta]
end omegaTerm

namespace countableOrd
def omega : countableOrd := ofPrincipal (.psi omegaTerm.one) -- lemma 6.8
end countableOrd


--===============================================================================
-- Comparison
--===============================================================================
/-
The comparison of two ψ functions is given in lemma 3.3. That is,
  (i) given α < β < ε_{Ω+1}, ψ(α) < ψ(β) iff α^* < ψ(β)
  (ii) given β < α < ε_{Ω+1}, ψ(α) < ψ(β) iff ψ(α) ≤ β^*
to represent these two statements, we consider the follwing equivalent statements:
  (i*) α^* < ψ(β) iff ∀ c ∈ C(α), c < ψ(β)
  (ii*)  ψ(α) ≤ β^* iff ∃ c ∈ C(β), ψ(α) < c or ψ(α) = c
-/
mutual
inductive countableOrd_lt : countableOrd → countableOrd → Prop where
  | sum {xs ys : List principal} (h : principalList_lt xs ys) :
        countableOrd_lt (countableOrd.sum xs) (countableOrd.sum ys)
inductive countableOrd_eq : countableOrd → countableOrd → Prop where
  | sum {xs ys : List principal} (h : principalList_eq xs ys) :
        countableOrd_eq (countableOrd.sum xs) (countableOrd.sum ys)
inductive principal_lt : principal → principal → Prop where
  | psi_forward {a b : omegaTerm} (h1 : omegaTerm_lt a b)
      (h2 : coefficientList_lt (omegaTerm.coefficients a) (countableOrd.ofPrincipal (.psi b))) :
                principal_lt (.psi a) (.psi b)
  | psi_reverse_lt {a b : omegaTerm} {c : countableOrd} (h1 : omegaTerm_lt b a)
                   (h2 : c ∈ omegaTerm.coefficients b)
                   (h3 : countableOrd_lt (countableOrd.ofPrincipal (.psi a)) c) :
                  principal_lt (.psi a) (.psi b)
  | psi_reverse_eq {a b : omegaTerm} {c : countableOrd} (h1 : omegaTerm_lt b a)
                   (h2 : c ∈ omegaTerm.coefficients b)
                   (h3 : countableOrd_eq (countableOrd.ofPrincipal (.psi a)) c) :
                  principal_lt (.psi a) (.psi b)
inductive principal_eq : principal → principal → Prop where
  | psi {a b : omegaTerm} (h : omegaTerm_eq a b) : principal_eq (.psi a) (.psi b)
inductive principalList_lt : List principal → List principal → Prop where
  | nil {p : principal} {ps : List principal} : principalList_lt [] (p :: ps)
  | head {p q : principal} {ps qs : List principal} (h : principal_lt p q) :
         principalList_lt (p :: ps) (q :: qs)
  | tail {p q : principal} {ps qs : List principal} (h1 : principal_eq p q)
         (h2 : principalList_lt ps qs) : principalList_lt (p :: ps) (q :: qs)
inductive principalList_eq : List principal → List principal → Prop where
  | nil : principalList_eq [] []
  | cons {p q : principal} {ps qs : List principal} (h1 : principal_eq p q)
         (h2 : principalList_eq ps qs) : principalList_eq (p :: ps) (q :: qs)
inductive omegaTerm_lt : omegaTerm → omegaTerm → Prop where
  | zero {alpha gamma : omegaTerm} {beta : countableOrd} :
         omegaTerm_lt omegaTerm.zero (omegaTerm.omegaNF alpha beta gamma)
  | exponent {alpha1 alpha2 gamma1 gamma2 : omegaTerm} {beta1 beta2 : countableOrd}
         (h : omegaTerm_lt alpha1 alpha2) :
         omegaTerm_lt (omegaTerm.omegaNF alpha1 beta1 gamma1)
                      (omegaTerm.omegaNF alpha2 beta2 gamma2)
  | coefficient {alpha1 alpha2 gamma1 gamma2 : omegaTerm} {beta1 beta2 : countableOrd}
         (h1 : omegaTerm_eq alpha1 alpha2) (h2 : countableOrd_lt beta1 beta2) :
         omegaTerm_lt (omegaTerm.omegaNF alpha1 beta1 gamma1)
                      (omegaTerm.omegaNF alpha2 beta2 gamma2)
  | remainder {alpha1 alpha2 gamma1 gamma2 : omegaTerm} {beta1 beta2 : countableOrd}
         (h1 : omegaTerm_eq alpha1 alpha2) (h2 : countableOrd_eq beta1 beta2)
         (h3 : omegaTerm_lt gamma1 gamma2) :
         omegaTerm_lt (omegaTerm.omegaNF alpha1 beta1 gamma1)
                      (omegaTerm.omegaNF alpha2 beta2 gamma2)
inductive omegaTerm_eq : omegaTerm → omegaTerm → Prop where
  | zero : omegaTerm_eq omegaTerm.zero omegaTerm.zero
  | omegaNF {alpha1 alpha2 gamma1 gamma2 : omegaTerm} {beta1 beta2 : countableOrd}
            (h1 : omegaTerm_eq alpha1 alpha2) (h2 : countableOrd_eq beta1 beta2)
            (h3 : omegaTerm_eq gamma1 gamma2) :
            omegaTerm_eq (omegaTerm.omegaNF alpha1 beta1 gamma1)
                         (omegaTerm.omegaNF alpha2 beta2 gamma2)
inductive coefficientList_lt : List countableOrd → countableOrd → Prop where
  | nil {bound : countableOrd} : coefficientList_lt [] bound
  | cons {c bound : countableOrd} {cs : List countableOrd} (hhead : countableOrd_lt c bound)
         (htail : coefficientList_lt cs bound) :
         coefficientList_lt (c :: cs) bound
end
infix:50 "<c" => countableOrd_lt
infix:50 "=c" => countableOrd_eq
infix:50 "<p" => principal_lt
infix:50 "=p" => principal_eq
infix:50 "<o" => omegaTerm_lt
infix:50 "=o" => omegaTerm_eq

def countableOrd_le (a b : countableOrd) : Prop :=
  countableOrd_lt a b ∨ countableOrd_eq a b
def principal_le (a b : principal) : Prop :=
  principal_lt a b ∨ principal_eq a b
def principalList_le (a b : List principal) : Prop :=
  principalList_lt a b ∨ principalList_eq a b
def principal_ge (a b : principal) : Prop :=
  principal_lt b a ∨ principal_eq a b
def omegaTerm_le (a b : omegaTerm) : Prop :=
  omegaTerm_lt a b ∨ omegaTerm_eq a b
infix:50 "≤c" => countableOrd_le
infix:50 "≤p" => principal_le
infix:50 "≥p" => principal_ge
infix:50 "≤o" => omegaTerm_le


--===============================================================================
-- Normality
--===============================================================================
/-
Just like the conditions for a valid Cantor Normal Form, we inspect the validity, or
normality of a ψ-function here.
-/
mutual
-- Normal if the list of principal sum is in decreasing normal form
inductive countableOrd_normal : countableOrd → Prop where
  | sum {ps : List principal} (h : principalList_normal ps) : countableOrd_normal (.sum ps)
-- Normal if the argument α of ψ(α) is normal
inductive principal_normal : principal → Prop where
  | psi {a : omegaTerm} (harg : omegaTerm_normal a)
      (hcoeff : coefficientList_lt (omegaTerm.coefficients a) (countableOrd.ofPrincipal (.psi a))) :
      principal_normal (.psi a)
-- Normal if each principal is normal and the list is in nonincreasing order
inductive principalList_normal : List principal → Prop where
  | nil : principalList_normal []
  | singleton {p : principal} (h : principal_normal p) : principalList_normal [p]
  | cons {p q : principal} {qs : List principal} (h1 : principal_normal p)
         (h2 : principalList_normal (q :: qs)) (h3 : p ≥p q) :
         principalList_normal (p :: q :: qs)
/-
Ω^{α}β + γ is normal if
  (i) α is normal
  (ii) β is normal positive countable (0 < β < Ω)
  (iii) γ is normal
  (iv) γ < Ω^{α}
-/
inductive omegaTerm_normal : omegaTerm → Prop where
  | zero : omegaTerm_normal .zero
  | omegaNF {alpha gamma : omegaTerm} {beta : countableOrd}
            (h1 : omegaTerm_normal alpha)
            (h2 : countableOrd_normal beta)
            (h3 : omegaTerm_normal gamma)
            (h4 : countableOrd.zero <c beta)
            (h5 : gamma <o .omegaNF alpha (countableOrd.one) (omegaTerm.zero)) :
      omegaTerm_normal (.omegaNF alpha beta gamma)
end


--===============================================================================
-- Some verification

theorem countableOrd_zero_lt_one :
    countableOrd.zero <c countableOrd.one := by
  simpa [countableOrd.zero, countableOrd.one, countableOrd.ofPrincipal]
  using countableOrd_lt.sum (principalList_lt.nil (p := principal.one) (ps := []))
theorem countableOrd_zero_normal :
    countableOrd_normal countableOrd.zero := by
  exact countableOrd_normal.sum principalList_normal.nil
theorem principal_one_normal : principal_normal principal.one := by
  apply principal_normal.psi
  · exact omegaTerm_normal.zero
  · change coefficientList_lt
      [countableOrd.zero]
      countableOrd.one
    exact coefficientList_lt.cons
      countableOrd_zero_lt_one
      coefficientList_lt.nil
theorem countableOrd_one_normal : countableOrd_normal countableOrd.one := by
  exact countableOrd_normal.sum (principalList_normal.singleton principal_one_normal)
theorem omegaTerm_one_normal : omegaTerm_normal omegaTerm.one := by
  change omegaTerm_normal (.omegaNF
      omegaTerm.zero
      countableOrd.one
      omegaTerm.zero)
  apply omegaTerm_normal.omegaNF
  · exact omegaTerm_normal.zero
  · exact countableOrd_one_normal
  · exact omegaTerm_normal.zero
  · exact countableOrd_zero_lt_one
  · exact omegaTerm_lt.zero
theorem bigOmega_normal :
    omegaTerm_normal omegaTerm.bigOmega := by
  change omegaTerm_normal
    (.omegaNF
      omegaTerm.one
      countableOrd.one
      omegaTerm.zero)
  apply omegaTerm_normal.omegaNF
  · exact omegaTerm_one_normal
  · exact countableOrd_one_normal
  · exact omegaTerm_normal.zero
  · exact countableOrd_zero_lt_one
  · exact omegaTerm_lt.zero

--===============================================================================
-- Irreflexivity of <
--===============================================================================
mutual
theorem countableOrd_lt_irrefl {a : countableOrd} (h : a<ca) : False := by
  cases h with
  | sum list => exact principalList_lt_irrefl list
theorem principal_lt_irrefl {a : principal} (h : a<pa) : False := by
  cases a with
  | psi o =>
      cases h with
      | psi_forward ho _ => exact omegaTerm_lt_irrefl ho
      | psi_reverse_lt ho _ _ => exact omegaTerm_lt_irrefl ho
      | psi_reverse_eq ho _ _ => exact omegaTerm_lt_irrefl ho
theorem principalList_lt_irrefl {l : List principal} (h : principalList_lt l l) : False := by
  cases h with
  | head h1 => exact principal_lt_irrefl h1
  | tail _ h2 => exact principalList_lt_irrefl h2
theorem omegaTerm_lt_irrefl {om : omegaTerm} (h : om <o om) : False := by
  cases h with
  | exponent h1 => exact omegaTerm_lt_irrefl h1
  | coefficient _ h2 => exact countableOrd_lt_irrefl h2
  | remainder _ _ h3 => exact omegaTerm_lt_irrefl h3
end


--===============================================================================
-- Symmetry of =
--===============================================================================
mutual
theorem countableOrd_eq_sym {a b : countableOrd} (h : a=cb) : b =c a :=by
  cases h with
  | sum h1 => exact countableOrd_eq.sum (principalList_eq_sym h1)
theorem principal_eq_sym {a b : principal} (h : a =p b) : b =p a := by
  cases h with
  | psi h1 => exact principal_eq.psi (omegaTerm_eq_sym h1)
theorem principalList_eq_sym {as bs : List principal} (h : principalList_eq as bs) :
        principalList_eq bs as := by
  cases h with
  | nil => exact principalList_eq.nil
  | cons head tail => exact
                      principalList_eq.cons (principal_eq_sym head) (principalList_eq_sym tail)
theorem omegaTerm_eq_sym {o1 o2 : omegaTerm} (h : o1 =o o2) : o2 =o o1 := by
  cases h with
  | zero => exact omegaTerm_eq.zero
  | omegaNF alpha beta gamma => exact omegaTerm_eq.omegaNF (omegaTerm_eq_sym alpha)
                                      (countableOrd_eq_sym beta) (omegaTerm_eq_sym gamma)
end

--===============================================================================
-- Structural Complexity
--===============================================================================
/-
We attempted to prove the trichotomy of each definition (countableOrd, principal, List principal,
and omegaTerm). But we ended up with a circular proof without termination, and this does not
work. We attempt a different approach by measuring the synctactic complexity of our
expressions. Concretely,
countableOrd : Given countableOrd.sum ps
               (i) complexity of each principal in ps,
               (ii) complexity of the list structure ps
               (iii) +1 for the sum constructor
principal : Given principal.psi o
            (i) complexity of argument o
            (ii) +1 for the psi constructor
List principal : Given p :: ps
                 (i) complexity of principal p
                 (ii) complexity of principal list ps
                 (iii) +1 for the list constructor
omegaTerm : Given omegaTerm.zero 4
            Given omegaTerm.omegaNF alpha beta gamma
            (i) complexity of omegaTerm alpha
            (ii) complexity of omegaTerm beta
            (iii) complexity of omegaTerm gamma
            (iv) +1 for the constructor

-/
mutual
  def countableOrd_cmplx (a : countableOrd) : Nat :=
    match a with
    | .sum ps => principalList_cmplx ps + 1
  termination_by
    sizeOf a
  decreasing_by
    all_goals simp_wf

  def principal_cmplx (p : principal) : Nat :=
    match p with
    | .psi o => omegaTerm_cmplx o + 1
  termination_by
    sizeOf p
  decreasing_by
    all_goals simp_wf

  def principalList_cmplx (ps : List principal) : Nat :=
    match ps with
    | [] => 0
    | q :: qs =>
        principal_cmplx q + principalList_cmplx qs + 1
  termination_by
    sizeOf ps
  decreasing_by
    all_goals simp_wf <;> omega

  def omegaTerm_cmplx (o : omegaTerm) : Nat :=
    match o with
    | .zero => 4
    | .omegaNF a b c =>
        omegaTerm_cmplx a
          + countableOrd_cmplx b
          + omegaTerm_cmplx c
          + 1
  termination_by
    sizeOf o
  decreasing_by
    all_goals simp_wf <;> omega
end
def coefficientList_cmplx : List countableOrd → Nat
  | [] => 0
  | c :: cs => countableOrd_cmplx c + coefficientList_cmplx cs + 1
theorem coefficientList_cmplx_append (xs ys : List countableOrd) :
        coefficientList_cmplx (xs ++ ys) = coefficientList_cmplx xs + coefficientList_cmplx ys
        := by
  induction xs with
  | nil => simp [coefficientList_cmplx]
  | cons x xs ih => simp only [List.cons_append, coefficientList_cmplx, ih]
                    omega
theorem coefficients_cmplx_lt (o : omegaTerm) : coefficientList_cmplx (omegaTerm.coefficients o) + 1
                                                < omegaTerm_cmplx o := by
  cases o with
  | zero =>
      simp [
        omegaTerm.coefficients,
        coefficientList_cmplx,
        countableOrd.zero,
        countableOrd_cmplx,
        principalList_cmplx,
        omegaTerm_cmplx
      ]
  | omegaNF alpha beta gamma =>
      have hAlpha := coefficients_cmplx_lt alpha
      have hGamma := coefficients_cmplx_lt gamma
      simp only [
        omegaTerm.coefficients,
        coefficientList_cmplx_append,
        coefficientList_cmplx,
        omegaTerm_cmplx
      ]
      omega
termination_by structural o

theorem coefficientList_member_cmplx_lt {c : countableOrd} {cs : List countableOrd} (hc : c ∈ cs) :
        countableOrd_cmplx c < coefficientList_cmplx cs := by
  induction cs with
  | nil => simp at hc
  | cons x xs ih =>
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only [coefficientList_cmplx]
      omega
    · have h := ih hc
      simp only [coefficientList_cmplx]
      omega
theorem coefficient_cmplx_lt_of_mem {o : omegaTerm} {c : countableOrd}
        (hc : c ∈ omegaTerm.coefficients o) :
        countableOrd_cmplx c + 2 < omegaTerm_cmplx o := by
  have hmem : countableOrd_cmplx c < coefficientList_cmplx (omegaTerm.coefficients o) :=
    coefficientList_member_cmplx_lt hc
  have hall := coefficients_cmplx_lt o
  omega

--===============================================================================
-- Trichotomy of < and =
--===============================================================================
mutual
theorem countableOrd_tri (a b : countableOrd) : a<cb ∨ a=cb ∨ b<ca := by
  cases a with
    | sum alist => cases b with
                    | sum blist =>
                      cases principalList_tri alist blist with
                        | inl hxy => exact Or.inl (countableOrd_lt.sum hxy)
                        | inr hrest =>
                          cases hrest with
                            | inl heq => exact Or.inr (Or.inl (countableOrd_eq.sum heq))
                            | inr hyx => exact Or.inr (Or.inr (countableOrd_lt.sum hyx))
  termination_by
    countableOrd_cmplx a + countableOrd_cmplx b
  decreasing_by
    all_goals
      simp only [countableOrd_cmplx]
      omega

theorem principal_tri (a b : principal) : a<pb ∨ a=pb ∨ b<pa := by
  cases a with
  | psi o1 =>
    cases b with
    | psi o2 =>
      cases omegaTerm_tri o1 o2 with
      | inl hxy =>
        cases coefficientList_tri (omegaTerm.coefficients o1)
              (countableOrd.ofPrincipal (.psi o2)) with
        | inl hcoeff => exact Or.inl (principal_lt.psi_forward hxy hcoeff)
        | inr hwitness =>
          obtain ⟨c, hc, hcomp⟩ := hwitness
          cases hcomp with
          | inl hlt => exact Or.inr (Or.inr (principal_lt.psi_reverse_lt hxy hc hlt))
          | inr heq => exact Or.inr (Or.inr (principal_lt.psi_reverse_eq hxy hc heq))
      | inr hrest =>
        cases hrest with
        | inl heq => exact Or.inr (Or.inl (principal_eq.psi heq))
        | inr hyx =>
          cases coefficientList_tri (omegaTerm.coefficients o2)
                (countableOrd.ofPrincipal (.psi o1)) with
          | inl hcoeff => exact Or.inr (Or.inr (principal_lt.psi_forward hyx hcoeff))
          | inr hwitness =>
            obtain ⟨c, hc, hcomp⟩ := hwitness
            cases hcomp with
            | inl hlt => exact Or.inl (principal_lt.psi_reverse_lt hyx hc hlt)
            | inr hequ =>exact Or.inl (principal_lt.psi_reverse_eq hyx hc hequ)
  termination_by
    principal_cmplx a + principal_cmplx b
  decreasing_by
    all_goals
      have h1 := coefficients_cmplx_lt o1
      have h2 := coefficients_cmplx_lt o2
      simp only [
        principal_cmplx,
        countableOrd.ofPrincipal,
        countableOrd_cmplx,
        principalList_cmplx
      ] at *
      omega


theorem principalList_tri (as bs : List principal) : principalList_lt as bs ∨
        principalList_eq as bs ∨ principalList_lt bs as := by
  cases as with
  | nil =>
      cases bs with
      | nil => exact Or.inr (Or.inl principalList_eq.nil)
      | cons b btail => exact Or.inl principalList_lt.nil
  | cons a atail =>
      cases bs with
      | nil => exact Or.inr (Or.inr principalList_lt.nil)
      | cons b btail =>
          cases principal_tri a b with
          | inl hab => exact Or.inl (principalList_lt.head hab)
          | inr hrest =>
              cases hrest with
              | inl heq =>
                  cases principalList_tri atail btail with
                  | inl htail =>
                      exact Or.inl
                        (principalList_lt.tail heq htail)
                  | inr htailrest =>
                      cases htailrest with
                      | inl htaileq =>
                          exact Or.inr
                            (Or.inl
                              (principalList_eq.cons
                                heq
                                htaileq))
                      | inr htailrev =>
                          exact Or.inr
                            (Or.inr
                              (principalList_lt.tail
                                (principal_eq_sym heq)
                                htailrev))
              | inr hba =>
                  exact Or.inr
                    (Or.inr
                      (principalList_lt.head hba))
termination_by
  principalList_cmplx as + principalList_cmplx bs
decreasing_by
  all_goals
    simp [principalList_cmplx]
    omega
theorem omegaTerm_tri (o1 o2 : omegaTerm) : o1<oo2 ∨ o1=oo2 ∨ o2<oo1 := by
  cases o1 with
  | zero =>
    cases o2 with
    | zero => exact Or.inr (Or.inl omegaTerm_eq.zero)
    | omegaNF a1 b1 c1 => exact Or.inl omegaTerm_lt.zero
  | omegaNF a2 b2 c2 =>
    cases o2 with
    | zero => exact Or.inr (Or.inr omegaTerm_lt.zero)
    | omegaNF a3 b3 c3 =>
      cases omegaTerm_tri a2 a3 with
      | inl h23 => exact Or.inl (omegaTerm_lt.exponent h23)
      | inr hrest =>
        cases hrest with
        | inl h23eq =>
          cases countableOrd_tri b2 b3 with
          | inl hb2b3 => exact Or.inl (omegaTerm_lt.coefficient h23eq hb2b3)
          | inr hbrest =>
            cases hbrest with
            | inl hbeq =>
              cases omegaTerm_tri c2 c3 with
              | inl hc23 => exact Or.inl (omegaTerm_lt.remainder h23eq hbeq hc23)
              | inr hcrest =>
                cases hcrest with
                | inl hceq => exact Or.inr (Or.inl (omegaTerm_eq.omegaNF h23eq hbeq hceq))
                | inr hc32 => exact Or.inr (Or.inr (omegaTerm_lt.remainder (omegaTerm_eq_sym h23eq)
                                            (countableOrd_eq_sym hbeq) hc32))
            | inr hb3b2 => exact Or.inr (Or.inr (omegaTerm_lt.coefficient (omegaTerm_eq_sym h23eq)
                                          hb3b2))
        | inr ha3a2 => exact Or.inr (Or.inr (omegaTerm_lt.exponent ha3a2))
  termination_by
    omegaTerm_cmplx o1 + omegaTerm_cmplx o2
  decreasing_by
    all_goals
      simp only [omegaTerm_cmplx]
      omega
theorem coefficientList_tri
    (cs : List countableOrd)
    (bound : countableOrd) :
    coefficientList_lt cs bound ∨
      ∃ c, c ∈ cs ∧ (bound <c c ∨ bound =c c) := by
  cases cs with
  | nil =>
      left
      exact coefficientList_lt.nil

  | cons c cs =>
      cases countableOrd_tri bound c with
      | inl hbc =>
          right
          exact ⟨c, List.mem_cons_self, Or.inl hbc⟩

      | inr hrest =>
          cases hrest with
          | inl heq =>
              right
              exact ⟨c, List.mem_cons_self, Or.inr heq⟩

          | inr hcb =>
              cases coefficientList_tri cs bound with
              | inl htail =>
                  left
                  exact coefficientList_lt.cons hcb htail

              | inr hexists =>
                  cases hexists with
                  | intro d hd =>
                      cases hd with
                      | intro hd_mem hd_rel =>
                          right
                          exact ⟨
                            d,
                            List.mem_cons_of_mem c hd_mem,
                            hd_rel
                          ⟩
termination_by
  coefficientList_cmplx cs + countableOrd_cmplx bound
decreasing_by
  all_goals
    simp_wf
    simp [coefficientList_cmplx] <;>
    omega
end


--===============================================================================
-- Reflexitivity of =
--===============================================================================
theorem countableOrd_eq_refl (a : countableOrd) : a =c a := by
  cases countableOrd_tri a a with
  | inl hlt => exact False.elim (countableOrd_lt_irrefl hlt)
  | inr hrest =>
    cases hrest with
    | inl heq => exact heq
    | inr hrt => exact False.elim (countableOrd_lt_irrefl hrt)
theorem principal_eq_refl (p : principal) : p =p p := by
  cases principal_tri p p with
  | inl hlt => exact False.elim (principal_lt_irrefl hlt)
  | inr hrest =>
    cases hrest with
    | inl heq => exact heq
    | inr hrt => exact False.elim (principal_lt_irrefl hrt)
theorem principalList_eq_refl (ps : List principal) : principalList_eq ps ps := by
  cases principalList_tri ps ps with
  | inl hlt => exact False.elim (principalList_lt_irrefl hlt)
  | inr hrest =>
    cases hrest with
    | inl heq => exact heq
    | inr hrt => exact False.elim (principalList_lt_irrefl hrt)
theorem omegaTerm_eq_refl (o : omegaTerm) : o =o o := by
  cases omegaTerm_tri o o with
  | inl hlt => exact False.elim (omegaTerm_lt_irrefl hlt)
  | inr hrest =>
    cases hrest with
    | inl heq => exact heq
    | inr hrt => exact False.elim (omegaTerm_lt_irrefl hrt)

--===============================================================================
-- Transitivity of =
--===============================================================================
mutual
theorem countableOrd_eq_trans {a b c : countableOrd} (hab : a=cb) (hbc : b=cc) :
        a =c c := by
  cases hab with
  | sum habList =>
      cases hbc with
      | sum hbcList =>
          exact countableOrd_eq.sum
            (principalList_eq_trans habList hbcList)
theorem principal_eq_trans {a b c : principal} (hab : a =p b) (hbc : b =p c) :
        a =p c := by
  cases hab with
  | psi habOmega =>
      cases hbc with
      | psi hbcOmega =>
          exact principal_eq.psi
            (omegaTerm_eq_trans habOmega hbcOmega)
theorem principalList_eq_trans {as bs cs : List principal} (hab : principalList_eq as bs)
        (hbc : principalList_eq bs cs) : principalList_eq as cs := by
  cases hab with
  | nil =>
      cases hbc with
      | nil =>
          exact principalList_eq.nil
  | cons habHead habTail =>
      cases hbc with
      | cons hbcHead hbcTail =>
          exact principalList_eq.cons
            (principal_eq_trans habHead hbcHead)
            (principalList_eq_trans habTail hbcTail)
theorem omegaTerm_eq_trans {a b c : omegaTerm} (hab : a =o b) (hbc : b =o c) :
        a =o c := by
  cases hab with
  | zero =>
      cases hbc with
      | zero =>
          exact omegaTerm_eq.zero
  | omegaNF habAlpha habBeta habGamma =>
      cases hbc with
      | omegaNF hbcAlpha hbcBeta hbcGamma =>
          exact omegaTerm_eq.omegaNF
            (omegaTerm_eq_trans habAlpha hbcAlpha)
            (countableOrd_eq_trans habBeta hbcBeta)
            (omegaTerm_eq_trans habGamma hbcGamma)
end

--===============================================================================
-- Transitivity of <
--===============================================================================
-- Helper lemmas connecting principal terms with singleton countable sums.
theorem countableOrd_ofPrincipal_lt {p q : principal} (h : p<pq) :
    countableOrd.ofPrincipal p <c countableOrd.ofPrincipal q := by
  change countableOrd.sum [p] <c countableOrd.sum [q]
  exact countableOrd_lt.sum (principalList_lt.head h)

theorem countableOrd_ofPrincipal_eq {p q : principal} (h : p=pq) :
    countableOrd.ofPrincipal p =c countableOrd.ofPrincipal q := by
  change countableOrd.sum [p] =c countableOrd.sum [q]
  exact countableOrd_eq.sum
    (principalList_eq.cons h principalList_eq.nil)

theorem principal_lt_of_ofPrincipal_lt {p q : principal}
    (h : countableOrd.ofPrincipal p<ccountableOrd.ofPrincipal q) :
    p <p q := by
  change countableOrd.sum [p] <c countableOrd.sum [q] at h
  cases h with
  | sum hlist =>
      cases hlist with
      | head hp => exact hp
      | tail _ htail => cases htail

-- A coefficient-list bound applies to each member.
theorem coefficientList_lt_of_mem
    {cs : List countableOrd} {bound c : countableOrd}
    (h : coefficientList_lt cs bound) (hc : c ∈ cs) :
    c <c bound := by
  induction cs generalizing bound c with
  | nil => simp at hc
  | cons x xs ih =>
      cases h with
      | cons hhead htail =>
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact hhead
          · exact ih htail hc

-- Custom equality of omega terms transports membership in their coefficient lists.
theorem coefficients_mem_eq
    {o1 o2 : omegaTerm} (h : o1=oo2) {c : countableOrd}
    (hc : c ∈ omegaTerm.coefficients o1) :
    ∃ d, d ∈ omegaTerm.coefficients o2 ∧ c =c d := by
  cases h with
  | zero =>
      simp only [omegaTerm.coefficients, List.mem_singleton] at hc
      subst c
      exact ⟨
        countableOrd.zero,
        by simp [omegaTerm.coefficients],
        countableOrd_eq_refl countableOrd.zero
      ⟩
  | @omegaNF alpha1 alpha2 gamma1 gamma2 beta1 beta2
      hAlpha hBeta hGamma =>
      simp only [
        omegaTerm.coefficients,
        List.mem_append,
        List.mem_singleton
      ] at hc
      rcases hc with (hcAlpha | hcGamma) | hcBeta
      · obtain ⟨d, hd, hcd⟩ := coefficients_mem_eq hAlpha hcAlpha
        refine ⟨d, ?_, hcd⟩
        simp only [
          omegaTerm.coefficients,
          List.mem_append,
          List.mem_singleton
        ]
        exact Or.inl (Or.inl hd)
      · obtain ⟨d, hd, hcd⟩ := coefficients_mem_eq hGamma hcGamma
        refine ⟨d, ?_, hcd⟩
        simp only [
          omegaTerm.coefficients,
          List.mem_append,
          List.mem_singleton
        ]
        exact Or.inl (Or.inr hd)
      · subst c
        refine ⟨beta2, ?_, hBeta⟩
        simp [omegaTerm.coefficients]
  termination_by
    omegaTerm_cmplx o1 + omegaTerm_cmplx o2
  decreasing_by
    all_goals
      subst_vars
      simp [omegaTerm_cmplx] <;> omega

theorem coefficientList_lt_of_forall {cs : List countableOrd} {bound : countableOrd}
        (h : ∀ c, c ∈ cs → c<cbound) : coefficientList_lt cs bound := by
  induction cs with
  | nil => exact coefficientList_lt.nil
  | cons c cs ih =>
      apply coefficientList_lt.cons
      · exact h c List.mem_cons_self
      · apply ih
        intro d hd
        exact h d (List.mem_cons_of_mem c hd)

@[simp] theorem countableOrd_cmplx_ofPrincipal_psi (o : omegaTerm) :
    countableOrd_cmplx (countableOrd.ofPrincipal (.psi o)) =
      omegaTerm_cmplx o + 3 := by
  simp [
    countableOrd.ofPrincipal,
    countableOrd_cmplx,
    principalList_cmplx,
    principal_cmplx
  ]

/-
Before proving transitivity, we prove directly that strict comparison and our
custom equality cannot both hold.  This is structural: no transitivity theorem
is used here.  In particular, this lets the difficult principal case close an
impossible equality branch without making a non-decreasing recursive call.
-/
mutual
theorem countableOrd_lt_eq_false {a b : countableOrd}
    (hlt : a<cb) (heq : a=cb) : False := by
  cases hlt with
  | sum hltList =>
      cases heq with
      | sum heqList =>
          exact principalList_lt_eq_false hltList heqList
  termination_by countableOrd_cmplx a + countableOrd_cmplx b
  decreasing_by
    all_goals
      subst_vars
      simp only [countableOrd_cmplx]
      omega

theorem principal_lt_eq_false {a b : principal}
    (hlt : a <p b) (heq : a =p b) : False := by
  cases hlt with
  | psi_forward harg _ =>
      cases heq with
      | psi heqArg =>
          exact omegaTerm_lt_eq_false harg heqArg
  | psi_reverse_lt harg _ _ =>
      cases heq with
      | psi heqArg =>
          exact omegaTerm_lt_eq_false harg (omegaTerm_eq_sym heqArg)
  | psi_reverse_eq harg _ _ =>
      cases heq with
      | psi heqArg =>
          exact omegaTerm_lt_eq_false harg (omegaTerm_eq_sym heqArg)
  termination_by principal_cmplx a + principal_cmplx b
  decreasing_by
    all_goals
      subst_vars
      simp only [principal_cmplx]
      omega

theorem principalList_lt_eq_false {as bs : List principal}
    (hlt : principalList_lt as bs) (heq : principalList_eq as bs) : False := by
  cases hlt with
  | nil => cases heq
  | head hhead =>
      cases heq with
      | cons heqHead _ =>
          exact principal_lt_eq_false hhead heqHead
  | tail _ htail =>
      cases heq with
      | cons _ heqTail =>
          exact principalList_lt_eq_false htail heqTail
  termination_by principalList_cmplx as + principalList_cmplx bs
  decreasing_by
    all_goals
      subst_vars
      simp only [principalList_cmplx]
      omega

theorem omegaTerm_lt_eq_false {a b : omegaTerm}
    (hlt : a <o b) (heq : a =o b) : False := by
  cases hlt with
  | zero => cases heq
  | exponent hAlpha =>
      cases heq with
      | omegaNF heqAlpha _ _ =>
          exact omegaTerm_lt_eq_false hAlpha heqAlpha
  | coefficient _ hBeta =>
      cases heq with
      | omegaNF _ heqBeta _ =>
          exact countableOrd_lt_eq_false hBeta heqBeta
  | remainder _ _ hGamma =>
      cases heq with
      | omegaNF _ _ heqGamma =>
          exact omegaTerm_lt_eq_false hGamma heqGamma
  termination_by omegaTerm_cmplx a + omegaTerm_cmplx b
  decreasing_by
    all_goals
      subst_vars
      simp only [omegaTerm_cmplx]
      omega
end

mutual

theorem countableOrd_lt_trans {a b c : countableOrd}
    (hab : a<cb) (hbc : b<cc) :
    a <c c := by
  cases hab with
  | sum habList =>
      cases hbc with
      | sum hbcList =>
          exact countableOrd_lt.sum
            (principalList_lt_trans habList hbcList)
  termination_by
    countableOrd_cmplx a + countableOrd_cmplx b + countableOrd_cmplx c
  decreasing_by
    all_goals
      subst_vars
      try simp [countableOrd_cmplx, principalList_cmplx]
      omega

theorem countableOrd_lt_eq_trans {a b c : countableOrd}
    (hab : a<cb) (hbc : b=cc) :
    a <c c := by
  cases hab with
  | sum habList =>
      cases hbc with
      | sum hbcList =>
          exact countableOrd_lt.sum
            (principalList_lt_eq_trans habList hbcList)
  termination_by
    countableOrd_cmplx a + countableOrd_cmplx b + countableOrd_cmplx c
  decreasing_by
    all_goals
      subst_vars
      simp only [countableOrd_cmplx]
      omega

theorem countableOrd_eq_lt_trans {a b c : countableOrd}
    (hab : a =c b) (hbc : b <c c) :
    a <c c := by
  cases hab with
  | sum habList =>
      cases hbc with
      | sum hbcList =>
          exact countableOrd_lt.sum
            (principalList_eq_lt_trans habList hbcList)
  termination_by
    countableOrd_cmplx a + countableOrd_cmplx b + countableOrd_cmplx c
  decreasing_by
    all_goals
      subst_vars
      try simp [countableOrd_cmplx, principalList_cmplx]
      omega

theorem principal_lt_trans
    {p1 p2 p3 : principal}
    (h12 : p1 <p p2)
    (h23 : p2 <p p3) :
    p1 <p p3 := by
  cases p1 with
  | psi a =>
    cases p2 with
    | psi b =>
      cases p3 with
      | psi c =>
        have h12c :
            countableOrd.ofPrincipal (.psi a) <c
              countableOrd.ofPrincipal (.psi b) :=
          countableOrd_ofPrincipal_lt h12
        have h23c :
            countableOrd.ofPrincipal (.psi b) <c
              countableOrd.ofPrincipal (.psi c) :=
          countableOrd_ofPrincipal_lt h23

        cases h12 with
        | psi_forward h12Arg h12Coeff =>
          cases h23 with
          | psi_forward h23Arg _ =>
              apply principal_lt.psi_forward
              · exact omegaTerm_lt_trans h12Arg h23Arg
              · apply coefficientList_lt_of_forall
                intro d hd
                have hd12 :
                    d <c countableOrd.ofPrincipal (.psi b) :=
                  coefficientList_lt_of_mem h12Coeff hd
                exact countableOrd_lt_trans hd12 h23c

          | psi_reverse_lt _ h23Mem h23Bound =>
              cases omegaTerm_tri a c with
              | inl hac =>
                  apply principal_lt.psi_forward
                  · exact hac
                  · apply coefficientList_lt_of_forall
                    intro d hd
                    have hd12 :
                        d <c countableOrd.ofPrincipal (.psi b) :=
                      coefficientList_lt_of_mem h12Coeff hd
                    exact countableOrd_lt_trans hd12 h23c

              | inr hrest =>
                  cases hrest with
                  | inl hacEq =>
                      obtain ⟨d, hd, hxd⟩ :=
                        coefficients_mem_eq
                          (omegaTerm_eq_sym hacEq)
                          h23Mem
                      have hdPsiB :
                          d <c countableOrd.ofPrincipal (.psi b) :=
                        coefficientList_lt_of_mem h12Coeff hd
                      have hdX : d <c _ :=
                        countableOrd_lt_trans hdPsiB h23Bound
                      exact False.elim
                        (countableOrd_lt_eq_false
                          hdX
                          (countableOrd_eq_sym hxd))

                  | inr hca =>
                      exact principal_lt.psi_reverse_lt
                        hca
                        h23Mem
                        (countableOrd_lt_trans h12c h23Bound)

          | psi_reverse_eq _ h23Mem h23Bound =>
              cases omegaTerm_tri a c with
              | inl hac =>
                  apply principal_lt.psi_forward
                  · exact hac
                  · apply coefficientList_lt_of_forall
                    intro d hd
                    have hd12 :
                        d <c countableOrd.ofPrincipal (.psi b) :=
                      coefficientList_lt_of_mem h12Coeff hd
                    exact countableOrd_lt_trans hd12 h23c

              | inr hrest =>
                  cases hrest with
                  | inl hacEq =>
                      obtain ⟨d, hd, hxd⟩ :=
                        coefficients_mem_eq
                          (omegaTerm_eq_sym hacEq)
                          h23Mem
                      have hdPsiB :
                          d <c countableOrd.ofPrincipal (.psi b) :=
                        coefficientList_lt_of_mem h12Coeff hd
                      have hdX : d <c _ :=
                        countableOrd_lt_eq_trans hdPsiB h23Bound
                      exact False.elim
                        (countableOrd_lt_eq_false
                          hdX
                          (countableOrd_eq_sym hxd))

                  | inr hca =>
                      exact principal_lt.psi_reverse_lt
                        hca
                        h23Mem
                        (countableOrd_lt_eq_trans h12c h23Bound)

        | psi_reverse_lt h12Arg h12Mem h12Bound =>
          cases h23 with
          | psi_forward _ h23Coeff =>
              have hxPsiC :
                  _ <c countableOrd.ofPrincipal (.psi c) :=
                coefficientList_lt_of_mem h23Coeff h12Mem
              have h13 :
                  countableOrd.ofPrincipal (.psi a) <c
                    countableOrd.ofPrincipal (.psi c) :=
                countableOrd_lt_trans h12Bound hxPsiC
              exact principal_lt_of_ofPrincipal_lt h13

          | psi_reverse_lt h23Arg h23Mem h23Bound =>
              exact principal_lt.psi_reverse_lt
                (omegaTerm_lt_trans h23Arg h12Arg)
                h23Mem
                (countableOrd_lt_trans h12c h23Bound)

          | psi_reverse_eq h23Arg h23Mem h23Bound =>
              exact principal_lt.psi_reverse_lt
                (omegaTerm_lt_trans h23Arg h12Arg)
                h23Mem
                (countableOrd_lt_eq_trans h12c h23Bound)

        | psi_reverse_eq h12Arg h12Mem h12Bound =>
          cases h23 with
          | psi_forward _ h23Coeff =>
              have hxPsiC :
                  _ <c countableOrd.ofPrincipal (.psi c) :=
                coefficientList_lt_of_mem h23Coeff h12Mem
              have h13 :
                  countableOrd.ofPrincipal (.psi a) <c
                    countableOrd.ofPrincipal (.psi c) :=
                countableOrd_eq_lt_trans h12Bound hxPsiC
              exact principal_lt_of_ofPrincipal_lt h13

          | psi_reverse_lt h23Arg h23Mem h23Bound =>
              exact principal_lt.psi_reverse_lt
                (omegaTerm_lt_trans h23Arg h12Arg)
                h23Mem
                (countableOrd_lt_trans h12c h23Bound)

          | psi_reverse_eq h23Arg h23Mem h23Bound =>
              exact principal_lt.psi_reverse_lt
                (omegaTerm_lt_trans h23Arg h12Arg)
                h23Mem
                (countableOrd_lt_eq_trans h12c h23Bound)
  termination_by
    principal_cmplx p1 + principal_cmplx p2 + principal_cmplx p3 + 1
  decreasing_by
    all_goals
      subst_vars
      try have hd_cmplx := coefficient_cmplx_lt_of_mem hd
      try have h12Mem_cmplx := coefficient_cmplx_lt_of_mem h12Mem
      try have h23Mem_cmplx := coefficient_cmplx_lt_of_mem h23Mem
      simp only [
        principal_cmplx,
        countableOrd_cmplx_ofPrincipal_psi
      ] at *
      omega

theorem principal_lt_eq_trans
    {p1 p2 p3 : principal}
    (h12 : p1 <p p2)
    (h23 : p2 =p p3) :
    p1 <p p3 := by
  cases p1 with
  | psi a =>
    cases p2 with
    | psi b =>
      cases p3 with
      | psi c =>
        cases h23 with
        | psi hbc =>
          have hPsiEq :
              countableOrd.ofPrincipal (.psi b) =c
                countableOrd.ofPrincipal (.psi c) :=
            countableOrd_ofPrincipal_eq (principal_eq.psi hbc)

          cases h12 with
          | psi_forward h12Arg h12Coeff =>
              apply principal_lt.psi_forward
              · exact omegaTerm_lt_eq_trans h12Arg hbc
              · apply coefficientList_lt_of_forall
                intro d hd
                have hd_cmplx : countableOrd_cmplx d + 2 < omegaTerm_cmplx a :=
                  coefficient_cmplx_lt_of_mem hd
                have hdPsiB : d <c countableOrd.ofPrincipal (.psi b) :=
                  coefficientList_lt_of_mem h12Coeff hd
                exact countableOrd_lt_eq_trans hdPsiB hPsiEq

          | psi_reverse_lt h12Arg h12Mem h12Bound =>
              obtain ⟨d, hd, hcd⟩ := coefficients_mem_eq hbc h12Mem
              have h12Mem_cmplx : countableOrd_cmplx _ + 2 < omegaTerm_cmplx b :=
                coefficient_cmplx_lt_of_mem h12Mem
              have hd_cmplx : countableOrd_cmplx d + 2 < omegaTerm_cmplx c :=
                coefficient_cmplx_lt_of_mem hd
              exact principal_lt.psi_reverse_lt
                    (omegaTerm_eq_lt_trans (omegaTerm_eq_sym hbc) h12Arg)
                    hd
                    (countableOrd_lt_eq_trans h12Bound hcd)

          | psi_reverse_eq h12Arg h12Mem h12Bound =>
              obtain ⟨d, hd, hcd⟩ := coefficients_mem_eq hbc h12Mem
              have h12Mem_cmplx : countableOrd_cmplx _ + 2 < omegaTerm_cmplx b :=
                coefficient_cmplx_lt_of_mem h12Mem
              have hd_cmplx : countableOrd_cmplx d + 2 < omegaTerm_cmplx c :=
                coefficient_cmplx_lt_of_mem hd
              exact principal_lt.psi_reverse_eq
                   (omegaTerm_eq_lt_trans (omegaTerm_eq_sym hbc) h12Arg)
                    hd
                   (countableOrd_eq_trans h12Bound hcd)
  termination_by
  principal_cmplx p1 +
  principal_cmplx p2 +
  principal_cmplx p3 + 1
  decreasing_by
    all_goals
      subst_vars
      simp only [
        principal_cmplx,
        countableOrd_cmplx_ofPrincipal_psi
      ]
      omega

theorem principal_eq_lt_trans
    {p1 p2 p3 : principal}
    (h12 : p1 =p p2)
    (h23 : p2 <p p3) :
    p1 <p p3 := by
  cases p1 with
  | psi a =>
    cases p2 with
    | psi b =>
      cases p3 with
      | psi c =>
        cases h12 with
        | psi hab =>
          have hPsiEq :
              countableOrd.ofPrincipal (.psi a) =c
                countableOrd.ofPrincipal (.psi b) :=
            countableOrd_ofPrincipal_eq (principal_eq.psi hab)

          cases h23 with
          | psi_forward h23Arg h23Coeff =>
              apply principal_lt.psi_forward
              · exact omegaTerm_eq_lt_trans hab h23Arg
              · apply coefficientList_lt_of_forall
                intro d hd
                obtain ⟨e, he, hde⟩ :=
                  coefficients_mem_eq hab hd
                have hePsiC :
                    e <c countableOrd.ofPrincipal (.psi c) :=
                  coefficientList_lt_of_mem h23Coeff he
                exact countableOrd_eq_lt_trans hde hePsiC

          | psi_reverse_lt h23Arg h23Mem h23Bound =>
              exact principal_lt.psi_reverse_lt
                (omegaTerm_lt_eq_trans
                  h23Arg
                  (omegaTerm_eq_sym hab))
                h23Mem
                (countableOrd_eq_lt_trans hPsiEq h23Bound)

          | psi_reverse_eq h23Arg h23Mem h23Bound =>
              exact principal_lt.psi_reverse_eq
                (omegaTerm_lt_eq_trans
                  h23Arg
                  (omegaTerm_eq_sym hab))
                h23Mem
                (countableOrd_eq_trans hPsiEq h23Bound)
  termination_by
    principal_cmplx p1 + principal_cmplx p2 + principal_cmplx p3 + 1
  decreasing_by
    all_goals
      subst_vars

      try have hd_cmplx := coefficient_cmplx_lt_of_mem hd
      try have he_cmplx := coefficient_cmplx_lt_of_mem he
      try have h23Mem_cmplx :=
        coefficient_cmplx_lt_of_mem h23Mem

      simp only [
        principal_cmplx,
        countableOrd_cmplx_ofPrincipal_psi
      ]

      omega

theorem principalList_lt_trans
    {pl1 pl2 pl3 : List principal}
    (h12 : principalList_lt pl1 pl2)
    (h23 : principalList_lt pl2 pl3) :
    principalList_lt pl1 pl3 := by
  cases h12 with
  | nil =>
      cases h23 with
      | head _ => exact principalList_lt.nil
      | tail _ _ => exact principalList_lt.nil
  | head h12Head =>
      cases h23 with
      | head h23Head =>
          exact principalList_lt.head
            (principal_lt_trans h12Head h23Head)
      | tail h23Eq _ =>
          exact principalList_lt.head
            (principal_lt_eq_trans h12Head h23Eq)
  | tail h12Eq h12Tail =>
      cases h23 with
      | head h23Head =>
          exact principalList_lt.head
            (principal_eq_lt_trans h12Eq h23Head)
      | tail h23Eq h23Tail =>
          exact principalList_lt.tail
            (principal_eq_trans h12Eq h23Eq)
            (principalList_lt_trans h12Tail h23Tail)
  termination_by
    principalList_cmplx pl1 + principalList_cmplx pl2 + principalList_cmplx pl3
  decreasing_by
    all_goals
      subst_vars
      try simp [principalList_cmplx]
      omega

theorem principalList_lt_eq_trans
    {pl1 pl2 pl3 : List principal}
    (h12 : principalList_lt pl1 pl2)
    (h23 : principalList_eq pl2 pl3) :
    principalList_lt pl1 pl3 := by
  cases h12 with
  | nil =>
      cases h23 with
      | cons _ _ => exact principalList_lt.nil
  | head h12Head =>
      cases h23 with
      | cons h23HeadEq _ =>
          exact principalList_lt.head
            (principal_lt_eq_trans h12Head h23HeadEq)
  | tail h12HeadEq h12Tail =>
      cases h23 with
      | cons h23HeadEq h23TailEq =>
          exact principalList_lt.tail
            (principal_eq_trans h12HeadEq h23HeadEq)
            (principalList_lt_eq_trans h12Tail h23TailEq)
  termination_by
    principalList_cmplx pl1 + principalList_cmplx pl2 + principalList_cmplx pl3
  decreasing_by
    all_goals
      subst_vars
      try simp [principalList_cmplx]
      omega

theorem principalList_eq_lt_trans
    {pl1 pl2 pl3 : List principal}
    (h12 : principalList_eq pl1 pl2)
    (h23 : principalList_lt pl2 pl3) :
    principalList_lt pl1 pl3 := by
  cases h12 with
  | nil =>
      cases h23 with
      | nil => exact principalList_lt.nil
  | cons h12Head h12Tail =>
      cases h23 with
      | head h23Head =>
          exact principalList_lt.head
            (principal_eq_lt_trans h12Head h23Head)
      | tail h23HeadEq h23Tail =>
          exact principalList_lt.tail
            (principal_eq_trans h12Head h23HeadEq)
            (principalList_eq_lt_trans h12Tail h23Tail)
  termination_by
    principalList_cmplx pl1 + principalList_cmplx pl2 + principalList_cmplx pl3
  decreasing_by
    all_goals
      subst_vars
      try simp [principalList_cmplx]
      omega

theorem omegaTerm_lt_eq_trans
    {o1 o2 o3 : omegaTerm}
    (h12 : o1 <o o2) (h23 : o2 =o o3) :
    o1 <o o3 := by
  cases h12 with
  | zero =>
      cases h23 with
      | omegaNF _ _ _ => exact omegaTerm_lt.zero
  | exponent h12Alpha =>
      cases h23 with
      | omegaNF h23Alpha _ _ =>
          exact omegaTerm_lt.exponent
            (omegaTerm_lt_eq_trans h12Alpha h23Alpha)
  | coefficient h12AlphaEq h12Coeff =>
      cases h23 with
      | omegaNF h23Alpha h23Coeff _ =>
          exact omegaTerm_lt.coefficient
            (omegaTerm_eq_trans h12AlphaEq h23Alpha)
            (countableOrd_lt_eq_trans h12Coeff h23Coeff)
  | remainder h12Alpha h12Beta h12Gamma =>
      cases h23 with
      | omegaNF h23Alpha h23Beta h23Gamma =>
          exact omegaTerm_lt.remainder
            (omegaTerm_eq_trans h12Alpha h23Alpha)
            (countableOrd_eq_trans h12Beta h23Beta)
            (omegaTerm_lt_eq_trans h12Gamma h23Gamma)
  termination_by
    omegaTerm_cmplx o1 + omegaTerm_cmplx o2 + omegaTerm_cmplx o3
  decreasing_by
    all_goals
      subst_vars
      try simp [
        omegaTerm_cmplx,
        countableOrd_cmplx,
        principalList_cmplx
      ]
      omega

theorem omegaTerm_eq_lt_trans
    {o1 o2 o3 : omegaTerm}
    (h12 : o1 =o o2) (h23 : o2 <o o3) :
    o1 <o o3 := by
  cases h12 with
  | zero =>
      cases h23 with
      | zero => exact omegaTerm_lt.zero
  | omegaNF h12Alpha h12Beta h12Gamma =>
      cases h23 with
      | exponent h23Alpha =>
          exact omegaTerm_lt.exponent
            (omegaTerm_eq_lt_trans h12Alpha h23Alpha)
      | coefficient h23Alpha h23Beta =>
          exact omegaTerm_lt.coefficient
            (omegaTerm_eq_trans h12Alpha h23Alpha)
            (countableOrd_eq_lt_trans h12Beta h23Beta)
      | remainder h23Alpha h23Beta h23Gamma =>
          exact omegaTerm_lt.remainder
            (omegaTerm_eq_trans h12Alpha h23Alpha)
            (countableOrd_eq_trans h12Beta h23Beta)
            (omegaTerm_eq_lt_trans h12Gamma h23Gamma)
  termination_by
    omegaTerm_cmplx o1 + omegaTerm_cmplx o2 + omegaTerm_cmplx o3
  decreasing_by
    all_goals
      subst_vars
      try simp [
        omegaTerm_cmplx,
        countableOrd_cmplx,
        principalList_cmplx
      ]
      omega

theorem omegaTerm_lt_trans
    {o1 o2 o3 : omegaTerm}
    (h12 : o1 <o o2) (h23 : o2 <o o3) :
    o1 <o o3 := by
  cases h12 with
  | zero =>
      cases h23 with
      | exponent _ => exact omegaTerm_lt.zero
      | coefficient _ _ => exact omegaTerm_lt.zero
      | remainder _ _ _ => exact omegaTerm_lt.zero
  | exponent h12Alpha =>
      cases h23 with
      | exponent h23Alpha =>
          exact omegaTerm_lt.exponent
            (omegaTerm_lt_trans h12Alpha h23Alpha)
      | coefficient h23Alpha _ =>
          exact omegaTerm_lt.exponent
            (omegaTerm_lt_eq_trans h12Alpha h23Alpha)
      | remainder h23Alpha _ _ =>
          exact omegaTerm_lt.exponent
            (omegaTerm_lt_eq_trans h12Alpha h23Alpha)
  | coefficient h12Alpha h12Beta =>
      cases h23 with
      | exponent h23Alpha =>
          exact omegaTerm_lt.exponent
            (omegaTerm_eq_lt_trans h12Alpha h23Alpha)
      | coefficient h23Alpha h23Beta =>
          exact omegaTerm_lt.coefficient
            (omegaTerm_eq_trans h12Alpha h23Alpha)
            (countableOrd_lt_trans h12Beta h23Beta)
      | remainder h23Alpha h23Beta _ =>
          exact omegaTerm_lt.coefficient
            (omegaTerm_eq_trans h12Alpha h23Alpha)
            (countableOrd_lt_eq_trans h12Beta h23Beta)
  | remainder h12Alpha h12Beta h12Gamma =>
      cases h23 with
      | exponent h23Alpha =>
          exact omegaTerm_lt.exponent
            (omegaTerm_eq_lt_trans h12Alpha h23Alpha)
      | coefficient h23Alpha h23Beta =>
          exact omegaTerm_lt.coefficient
            (omegaTerm_eq_trans h12Alpha h23Alpha)
            (countableOrd_eq_lt_trans h12Beta h23Beta)
      | remainder h23Alpha h23Beta h23Gamma =>
          exact omegaTerm_lt.remainder
            (omegaTerm_eq_trans h12Alpha h23Alpha)
            (countableOrd_eq_trans h12Beta h23Beta)
            (omegaTerm_lt_trans h12Gamma h23Gamma)
  termination_by
    omegaTerm_cmplx o1 + omegaTerm_cmplx o2 + omegaTerm_cmplx o3
  decreasing_by
    all_goals
      subst_vars
      try simp [
        omegaTerm_cmplx,
        countableOrd_cmplx,
        principalList_cmplx
      ]
      omega
end

--===============================================================================
-- Assymmetry of <
--===============================================================================
theorem countableOrd_lt_asymm {a b : countableOrd} (h : a<cb) : ¬ b<ca := by
  intro hba
  exact countableOrd_lt_irrefl (countableOrd_lt_trans h hba)

theorem principal_lt_asymm {p1 p2 : principal} (h : p1<pp2) : ¬ p2<pp1 := by
  intro h21
  exact principal_lt_irrefl (principal_lt_trans h h21)
theorem principalList_lt_asymm {pList1 pList2 : List principal}
        (h : principalList_lt pList1 pList2) :
        ¬ principalList_lt pList2 pList1 := by
  intro hList21
  exact principalList_lt_irrefl (principalList_lt_trans h hList21)
theorem omegaTerm_lt_asymm {o1 o2 : omegaTerm} (h : o1<oo2) : ¬ o2<oo1:= by
  intro h21
  exact omegaTerm_lt_irrefl (omegaTerm_lt_trans h h21)

/-
We have proven the irreflexitivity, asymmetry, and the transitivity of our defined comparison
relation. We also have the trichotomy of the relation. This concludes the justification for
our relation to be a linear ordering. We proceed to well-foundedness. Note, we were able to
show the linear ordering of our raw data type of countableOrd, principal, principalList,
and omegaTerm so a stronger version than that for normal data types.
-/


--===============================================================================
-- Normal Objects
--===============================================================================
/-
So far, the properties proven are for the raw data type. Mathematically, the objects
are not well-defined as normality of them is not included. We redefine the
proper objects here.
-/
abbrev NormalCountableOrd :=
  {a : countableOrd // countableOrd_normal a}
abbrev NormalPrincipal :=
  {p : principal // principal_normal p}
abbrev NormalOmegaTerm :=
  {o : omegaTerm // omegaTerm_normal o}
abbrev NormalPrincipalList :=
  {ps : List principal // principalList_normal ps}
def NormalCountableOrd_lt (a b : NormalCountableOrd) : Prop := a.1 <c b.1
def NormalCountableOrd_eq (a b : NormalCountableOrd) : Prop := a.1 =c b.1
def NormalPrincipal_lt (a b : NormalPrincipal) : Prop := a.1 <p b.1
def NormalPrincipal_eq
    (a b : NormalPrincipal) : Prop :=
  a.1 =p b.1
def NormalOmegaTerm_lt (a b : NormalOmegaTerm) : Prop := a.1 <o b.1
def NormalOmegaTerm_eq (a b : NormalOmegaTerm) : Prop := a.1 =o b.1
def NormalPrincipalList_lt (as bs : NormalPrincipalList) : Prop :=
  principalList_lt as.1 bs.1
def NormalPrincipalList_eq
    (as bs : NormalPrincipalList) : Prop :=
  principalList_eq as.1 bs.1
infix:50 " <nc " => NormalCountableOrd_lt
infix:50 " =nc " => NormalCountableOrd_eq
infix:50 "<np" => NormalPrincipal_lt
infix:50 "=np" => NormalPrincipal_eq
infix:50 "<no" => NormalOmegaTerm_lt
infix:50 "=no" => NormalOmegaTerm_eq

-- Prove the linear ordering for normal datas
-- Trichotomy
theorem NormalCountableOrd_tri (a b : NormalCountableOrd) :
    a <nc b ∨ a =nc b ∨ b <nc a := by
  exact countableOrd_tri a.1 b.1
theorem NormalPrincipal_tri (a b : NormalPrincipal) :
    a.1 <p b.1 ∨ a.1 =p b.1 ∨ b.1 <p a.1 := by
  exact principal_tri a.1 b.1
theorem NormalOmegaTerm_tri (a b : NormalOmegaTerm) :
    a.1 <o b.1 ∨ a.1 =o b.1 ∨ b.1 <o a.1 := by
  exact omegaTerm_tri a.1 b.1
theorem NormalPrincipalList_tri (as bs : NormalPrincipalList) :
    principalList_lt as.1 bs.1 ∨ principalList_eq as.1 bs.1 ∨
    principalList_lt bs.1 as.1 := by
  exact principalList_tri as.1 bs.1
-- Irreflexivity
theorem NormalCountableOrd_irrefl (a : NormalCountableOrd) :
    ¬ a <nc a := by
  intro h
  exact countableOrd_lt_irrefl h
theorem NormalPrincipal_irrefl (p : NormalPrincipal) :
    ¬ p <np p := by
  intro h
  exact principal_lt_irrefl h
theorem NormalPrincipalList_irrefl (pl : NormalPrincipalList) :
    ¬ (NormalPrincipalList_lt pl pl) :=  by
  intro h
  exact principalList_lt_irrefl h
theorem NormalOmegaTerm_irrefl (o : NormalOmegaTerm) :
    ¬ o<noo := by
  intro h
  exact omegaTerm_lt_irrefl h
-- Transitivity
theorem NormalCountableOrd_trans {a b c : NormalCountableOrd} (hab : a <nc b) (hbc : b <nc c) :
    a <nc c := by
  exact countableOrd_lt_trans hab hbc
theorem NormalPrincipal_trans {p1 p2 p3 : NormalPrincipal} (h12 : p1<npp2) (h23 : p2<npp3) :
    p1 <np p3 := by
  exact principal_lt_trans h12 h23
theorem NormalPrincipalList_trans {pl1 pl2 pl3 : NormalPrincipalList}
        (h12 : NormalPrincipalList_lt pl1 pl2)
        (h23 : NormalPrincipalList_lt pl2 pl3) : NormalPrincipalList_lt pl1 pl3 := by
  exact principalList_lt_trans h12 h23
theorem NormalOmegaTerm_trans {o1 o2 o3 : NormalOmegaTerm}
        (h12 : o1<noo2) (h23 : o2<noo3) : o1 <no o3 := by
  exact omegaTerm_lt_trans h12 h23
-- Assymetry
theorem NormalCountableOrd_asymm {a b : NormalCountableOrd} (h : a <nc b) : ¬ b <nc a := by
  intro con
  exact countableOrd_lt_asymm (a := a.1) (b := b.1) h con
theorem NormalPrincipal_asymm {p1 p2 : NormalPrincipal} (h : p1<npp2) : ¬ p2 <np p1 := by
  intro con
  exact principal_lt_asymm (p1 := p1.1) (p2 := p2.1) h con
theorem NormalPrincipalList_asymm {pl1 pl2 : NormalPrincipalList}
       (h : NormalPrincipalList_lt pl1 pl2) :
        ¬ NormalPrincipalList_lt pl2 pl1 := by
  intro con
  exact principalList_lt_asymm (pList1 := pl1.1) (pList2 := pl2.1) h con
theorem NormalOmegaTerm_asymm {o1 o2 : NormalOmegaTerm} (h : o1<noo2) : ¬ o2 <no o1 := by
  intro con
  exact omegaTerm_lt_asymm (o1 := o1.1) (o2 := o2.1) h con

--===============================================================================
-- Well-Foundedness
--===============================================================================
--Preliminaries
-- Given a NormalPrincipalList, its head is a NormalPrincipal
theorem NormalPrincipalList_normalHead {p : principal} {ps : List principal}
       (h : principalList_normal (p :: ps)) : principal_normal p := by
  cases h with
  | singleton h1 => exact h1
  | cons h2 h3 => exact h2
-- Given a normal principal list, its tail is normal
theorem NormalPrincipalList_normalTail {p : principal} {ps : List principal}
       (h : principalList_normal (p :: ps)) : principalList_normal ps := by
  cases h with
  | singleton h1 => exact principalList_normal.nil
  | cons h2 h3 => exact h3
-- Given a normal principal list, the head bounds all the elements of the list from above
theorem principalList_normal_tail_bounded {p : principal} {ps : List principal}
        (h : principalList_normal (p :: ps)) :
        ∀ q ∈ ps, q ≤p p := by
  induction ps generalizing p with
  | nil =>
      intro q hq
      cases hq
  | cons q qs ih =>
      cases h with
      | cons _ htail hpq =>
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · rcases hpq with hqp | hpq
            · exact Or.inl hqp
            · exact Or.inr (principal_eq_sym hpq)
          · have hrq : r ≤p q := ih htail r hr
            rcases hrq with hrq | hrq
            · rcases hpq with hqp | hpq
              · exact Or.inl (principal_lt_trans hrq hqp)
              · exact Or.inl
                  (principal_lt_eq_trans hrq (principal_eq_sym hpq))
            · rcases hpq with hqp | hpq
              · exact Or.inl (principal_eq_lt_trans hrq hqp)
              · exact Or.inr
                  (principal_eq_trans hrq (principal_eq_sym hpq))
-- Given omegaTerm (Ω^{α}β+γ), all α, β, γ are normal in their respective data type
-- alpha (exponent)
theorem omegaTerm_normal_alpha {alpha gamma : omegaTerm} {beta : countableOrd}
        (ho : omegaTerm_normal (.omegaNF alpha beta gamma)) :
        omegaTerm_normal alpha := by
  cases ho with
  | omegaNF h1 _ _ _ _ => exact h1
-- beta (coefficient)
theorem omegaTerm_normal_beta {alpha gamma : omegaTerm} {beta : countableOrd}
        (ho : omegaTerm_normal (.omegaNF alpha beta gamma)) :
        countableOrd_normal beta := by
  cases ho with
  | omegaNF _ h1 _ _ _ => exact h1
-- gamma (remainder)
theorem omegaTerm_normal_gamma {alpha gamma : omegaTerm} {beta : countableOrd}
        (ho : omegaTerm_normal (.omegaNF alpha beta gamma)) :
        omegaTerm_normal gamma := by
  cases ho with
  | omegaNF _ _ h1 _ _ => exact h1
-- Any element of the cofficients of a normal omegaTerm is normal
theorem coefficient_normal_of_mem {o : omegaTerm} {c : countableOrd}
    (ho : omegaTerm_normal o) (hc : c ∈ omegaTerm.coefficients o) :
    countableOrd_normal c := by
  cases o with
  | zero =>
      simp only [omegaTerm.coefficients, List.mem_singleton] at hc
      subst c
      exact countableOrd_zero_normal
  | omegaNF alpha beta gamma =>
      have hAlpha : omegaTerm_normal alpha := omegaTerm_normal_alpha ho
      have hBeta : countableOrd_normal beta := omegaTerm_normal_beta ho
      have hGamma : omegaTerm_normal gamma := omegaTerm_normal_gamma ho
      simp only [omegaTerm.coefficients, List.mem_append, List.mem_singleton] at hc
      rcases hc with (hcAlpha | hcGamma) | hcBeta
      · exact coefficient_normal_of_mem hAlpha hcAlpha
      · exact coefficient_normal_of_mem hGamma hcGamma
      · subst c
        exact hBeta
  termination_by omegaTerm_cmplx o
  decreasing_by
    all_goals
      subst_vars
      simp [omegaTerm_cmplx] <;> omega

/- If a NormalCountableOrd is accessible, any of that less than the original
   is accessible. Ones follow are analogous. -/
theorem NormalCountableOrd_acc_of_lt {a b : NormalCountableOrd}
        (ha : Acc NormalCountableOrd_lt a) (hba : b <nc a) :
        Acc NormalCountableOrd_lt b :=
  ha.inv hba
theorem NormalPrincipal_acc_of_lt {p1 p2 : NormalPrincipal}
        (h1 : Acc NormalPrincipal_lt p1) (h21 : p2<npp1) :
        Acc NormalPrincipal_lt p2 :=
  h1.inv h21
theorem NormalPrincipalList_acc_of_lt {pl1 pl2 : NormalPrincipalList}
        (h1 : Acc NormalPrincipalList_lt pl1) (h21 : NormalPrincipalList_lt pl2 pl1) :
        Acc NormalPrincipalList_lt pl2 :=
  h1.inv h21
theorem NormalOmegaTerm_acc_of_lt {o1 o2 : NormalOmegaTerm}
        (h1 : Acc NormalOmegaTerm_lt o1) (h21 : NormalOmegaTerm_lt o2 o1) :
        Acc NormalOmegaTerm_lt o2 :=
  h1.inv h21
theorem NormalCountableOrd_acc_of_eq {a b : NormalCountableOrd}
        (ha : Acc NormalCountableOrd_lt a) (hab : a =nc b) : Acc NormalCountableOrd_lt b := by
  apply Acc.intro --∀c:NormalCountableOrd, c <nc b → Acc <nc c
  intro c hcb -- Acc <nc c
  apply ha.inv -- c <nc a
  exact countableOrd_lt_eq_trans hcb (countableOrd_eq_sym hab)



def principalList_bounded_by (p : principal) (ps : List principal) : Prop :=
  ∀ q, q ∈ ps → q ≤p p
-- The empty list (of NormalPrincipalList) is accessible
theorem NormalPrincipalList_nil_acc : Acc NormalPrincipalList_lt ⟨[], principalList_normal.nil⟩
        := by
  apply Acc.intro
  rintro ⟨ps, hps⟩ hlt
  change principalList_lt ps [] at hlt
  cases hlt
-- If NormalPrincipal p is accessible and p = q, then q is accessible
theorem NormalPrincipal_acc_of_eq {p q : NormalPrincipal} (hp : Acc NormalPrincipal_lt p)
        (hpq : p=npq) : Acc NormalPrincipal_lt q := by
  apply Acc.intro -- ∀r<npq, Acc NormalPrincipal_lt r
  intro r hrq
  apply hp.inv
  exact principal_lt_eq_trans hrq (principal_eq_sym hpq)
-- Given a NormalPrincipalList p :: ps, if NormalPrincipalList qs such as qs<q<p is accessible, then
-- p :: ps is accessible
theorem NormalPrincipalList_cons_acc (p : NormalPrincipal) (hp : Acc NormalPrincipal_lt p)
        (hsmall : ∀q:NormalPrincipal, q<npp -> ∀qs : NormalPrincipalList,
                  principalList_bounded_by q.1 qs.1 → Acc NormalPrincipalList_lt qs)
        (ps : NormalPrincipalList)
        (hps : Acc NormalPrincipalList_lt ps)
        (hcons : principalList_normal (p.1 :: ps.1)) :
        Acc NormalPrincipalList_lt ⟨p.1 :: ps.1, hcons⟩ := by
  induction hps generalizing p with
  | intro xs hxs ih => -- xs:any<ps, hxs:Acc NormalPrincipalList_lt xs,
    apply Acc.intro; rintro ⟨ys, hys_normal⟩ hlt
    cases ys with
    | nil => exact NormalPrincipalList_nil_acc
    | cons q qs =>
      change principalList_lt (q :: qs) (p.1 :: xs.1) at hlt
      cases hlt with
      | head hqp =>
        let qN : NormalPrincipal :=
            ⟨q, NormalPrincipalList_normalHead hys_normal⟩
        apply hsmall qN hqp ⟨q :: qs, hys_normal⟩
        intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact Or.inr (principal_eq_refl r)
        · exact principalList_normal_tail_bounded hys_normal r hr
      | tail heq htail =>
        let qN : NormalPrincipal :=
            ⟨q, NormalPrincipalList_normalHead hys_normal⟩
        let qsN : NormalPrincipalList :=
            ⟨qs, NormalPrincipalList_normalTail hys_normal⟩
        have htailN : NormalPrincipalList_lt qsN xs := htail
        have hqAcc : Acc NormalPrincipal_lt qN := by
          apply NormalPrincipal_acc_of_eq hp
          exact principal_eq_sym heq
        have hsmallQ : ∀ r : NormalPrincipal, r <np qN →
                       ∀ rs : NormalPrincipalList,
                       principalList_bounded_by r.1 rs.1 →
                       Acc NormalPrincipalList_lt rs := by
          intro r hr rs hrs
          apply hsmall r
          · exact principal_lt_eq_trans hr heq
          · exact hrs
        exact ih qsN htailN
                qN
                hqAcc
                hsmallQ
                hys_normal

-- Given an accessible NormalPrincipal p, if ps < p, then NormalPrincipalList ps is accessible
theorem NormalPrincipalList_acc_of_bound_acc (p : NormalPrincipal) (hp : Acc NormalPrincipal_lt p)
    (ps : NormalPrincipalList) (hbound : principalList_bounded_by p.1 ps.1) :
    Acc NormalPrincipalList_lt ps := by
  revert ps -- Goal is ∀ps:NormalPrincipalList, principalList_bounded_by p.1 ps.1 →
            -- Acc NormalPrincipalList_lt ps
  induction hp with
  | intro p hpred ih => -- hpred:∀q<p, Acc NormalPrincipal_lt q
                        -- ih : ∀q,q<p → ∀ps, principalList_bounded_by p.1 ps.1
                        --      → Acc NormalPrincipalList_lt ps
    rintro ⟨ps, hps⟩ hbound -- Goal: Acc NormalPrincipalList_lt ⟨ps, hps⟩
    have proveList : ∀xs : List principal, ∀hxs : principalList_normal xs,
                     principalList_bounded_by p.1 xs
                     → Acc NormalPrincipalList_lt ⟨xs, hxs⟩ := by
      intro xs
      induction xs with
      | nil => intro hxs hbound; exact NormalPrincipalList_nil_acc
      -- ih : ∀hqs : principalList_normal qs, principalList_bounded_by p.1 qs →
      --      Acc NormalPrincipalList_lt ⟨qs, hqs⟩
      | cons q qs ihTail =>
        intro hnormal hbound -- hnormal:principalList_normal (q :: qs),
                             -- hbound:principalList_bounded_by p.1 (q :: qs)
        have hq_normal : principal_normal q := NormalPrincipalList_normalHead hnormal
        have hqs_normal : principalList_normal qs := NormalPrincipalList_normalTail hnormal
        let qN : NormalPrincipal := ⟨q, hq_normal⟩
        let qsN : NormalPrincipalList := ⟨qs, hqs_normal⟩
        have htailBound : principalList_bounded_by p.1 qs := by
          intro r hr
          exact hbound r (List.mem_cons_of_mem q hr)
        have htailAcc : Acc NormalPrincipalList_lt qsN :=
          ihTail hqs_normal htailBound
        have hqle : q ≤p p.1 :=
          hbound q List.mem_cons_self
        rcases hqle with hqp | hqeqp
        · have hqAcc : Acc NormalPrincipal_lt qN :=
               hpred qN hqp
          have hsmallQ :
                  ∀ r : NormalPrincipal, r <np qN →
                    ∀ rs : NormalPrincipalList,
                      principalList_bounded_by r.1 rs.1 →
                      Acc NormalPrincipalList_lt rs := by
                intro r hr rs hrs
                apply ih r
                · exact principal_lt_trans hr hqp
                · exact hrs
          exact NormalPrincipalList_cons_acc
                qN
                hqAcc
                hsmallQ
                qsN
                htailAcc
                hnormal
        · have hpAcc : Acc NormalPrincipal_lt p :=
            Acc.intro p hpred
          have hqAcc : Acc NormalPrincipal_lt qN := by
            apply NormalPrincipal_acc_of_eq hpAcc
            exact principal_eq_sym hqeqp
          have hsmallQ :
              ∀ r : NormalPrincipal, r <np qN →
                ∀ rs : NormalPrincipalList,
                  principalList_bounded_by r.1 rs.1 →
                  Acc NormalPrincipalList_lt rs := by
            intro r hr rs hrs
            apply ih r
            · exact principal_lt_eq_trans hr hqeqp
            · exact hrs
          exact NormalPrincipalList_cons_acc
            qN
            hqAcc
            hsmallQ
            qsN
            htailAcc
            hnormal
    exact proveList ps hps hbound

-- Given a NormalPrincipalList p :: ps, if the head is accessible, then the entire
-- list is accessible
theorem NormalPrincipalList_acc {p : principal} {ps : List principal}
        (hnormal : principalList_normal (p :: ps))
        (hp : Acc NormalPrincipal_lt ⟨p, NormalPrincipalList_normalHead hnormal⟩) :
        Acc NormalPrincipalList_lt ⟨p :: ps, hnormal⟩ := by
  let pnormal : NormalPrincipal := ⟨p, NormalPrincipalList_normalHead hnormal⟩
  apply NormalPrincipalList_acc_of_bound_acc pnormal hp ⟨p :: ps, hnormal⟩
  -- Goal now is ∀q, q∈p::ps, q ≤p p
  intro q hq
  simp only [List.mem_cons] at hq -- hq is q=p ∨ q∈ps
  rcases hq with hqp | hq
  · subst q
    exact Or.inr (principal_eq_refl p)
  · exact principalList_normal_tail_bounded hnormal q hq
-- Given an accessible NormalPrincipalList ps, then its countableOrd is accessible
theorem NormalCountableOrd_acc {ps : NormalPrincipalList} (hps : Acc NormalPrincipalList_lt ps) :
        Acc NormalCountableOrd_lt ⟨countableOrd.sum ps, countableOrd_normal.sum ps.2⟩ := by
  induction hps with
  -- hpred : ∀qs, qs<ps → Acc NormalPrincipalList_lt qs
  -- ih : ∀qs, qs<ps → Acc NormalCountableOrd_lt ⟨countableOrd.sum q.1,countableOrd_normal.sum qs.2⟩
  | intro ps hpred ih =>
    apply Acc.intro -- Goal changed : ∀qs:NormalCountableOrd, qs<⟨ps,--⟩ → Acc -- qs
    rintro ⟨a, ha⟩ hlt
    cases a with
    | sum qs =>
      cases ha with
      | sum hqsNormal =>
          cases hlt with
          | sum hqsLt =>
              exact ih ⟨qs, hqsNormal⟩ hqsLt
--==================================================================================================
theorem NormalOmegaTerm_acc_of_eq {a b : NormalOmegaTerm} (ha : Acc NormalOmegaTerm_lt a)
    (hab : a=nob) : Acc NormalOmegaTerm_lt b := by
  apply Acc.intro --Goal is ∀c:NormalOmegaTerm, c<ob → Acc NormalOmegaTerm_lt c
  intro c hcb
  apply ha.inv -- Goal c <o a
  exact omegaTerm_lt_eq_trans hcb (omegaTerm_eq_sym hab)
-- The countableOrd of normalprincipal p is normal
theorem countableOrd_ofPrincipal_normal {p : principal} (hp : principal_normal p) :
    countableOrd_normal (countableOrd.ofPrincipal p) := by
  apply countableOrd_normal.sum
  exact principalList_normal.singleton hp
-- If the NormalCountableOrd of a NormalPrincipal p is accessible, then p is accessible
theorem NormalPrincipal_acc_of_ofPrincipal_acc (p : NormalPrincipal)
        (hp : Acc NormalCountableOrd_lt ⟨countableOrd.ofPrincipal p.1,
                                         countableOrd_ofPrincipal_normal p.2⟩) :
        Acc NormalPrincipal_lt p := by
  let embed : NormalPrincipal → NormalCountableOrd :=
              fun q => ⟨countableOrd.ofPrincipal q.1, countableOrd_ofPrincipal_normal q.2⟩
  have embed_lt {q r : NormalPrincipal} (hqr : q<npr) : embed q <nc embed r := by
    change countableOrd.ofPrincipal q.1 <c countableOrd.ofPrincipal r.1
    exact countableOrd_lt.sum (principalList_lt.head hqr)
  have aux : ∀a : NormalCountableOrd, Acc NormalCountableOrd_lt a
             → ∀r : NormalPrincipal, embed r = a
             → Acc NormalPrincipal_lt r := by
    intro a ha
    induction ha with
    | intro a hpred ih => intro r hra
                          apply Acc.intro
                          intro q hqr
                          have hqa : embed q <nc a := by rw [← hra]; exact embed_lt hqr
                          exact ih (embed q) hqa q rfl
  exact aux (embed p) hp p rfl
-- The zero NormalOmegaTerm is accessible
theorem NormalOmegaTerm_zero_acc : Acc NormalOmegaTerm_lt
        ⟨omegaTerm.zero, omegaTerm_normal.zero⟩ := by
  apply Acc.intro -- Goal : ∀ o <no omegaTerm.zero → Acc NormalOmegaTerm_lt o
  rintro ⟨o, ho⟩ hlt
  change omegaTerm_lt o .zero at hlt
  cases hlt
--========================================================================================
-- Complexity (more in detail)
/-
With our current measure of complexity, it merely measures the tree of the given data. We encounter
a couple of issues in termination with this method for the case of proving accessibility.
Concretely, suppose we have the following omegaTerms :
  x = Ω^{α_small}β + γ
  y = Ω^{α_large}1 + 0
Since the old measurement compares the exponent first, we can have x <o y even though synctactically
(complexity of omegaTerm x) >> (complexity of omegaTerm y). So, we have a mismatch with our
measurement. This arises from the fact we represented complexity as one natural number but we
consider now the complexity as a triple. That is, if we name the complexity as "rank", we have
((rank of α), (rank of β), (rank of γ)) and compare them lexicographically.
-/
--========================================================================================

mutual

theorem NormalCountableOrd_all_acc (a : NormalCountableOrd) :
        Acc NormalCountableOrd_lt a := by
  rcases a with ⟨a_countableOrd, ha_isNormal⟩
  cases a_countableOrd with
  | sum ps =>
    cases ha_isNormal with
    | sum hps =>
      cases ps with
      | nil => exact NormalCountableOrd_acc NormalPrincipalList_nil_acc
      | cons p pList =>
        have hpNormal : principal_normal p :=
          NormalPrincipalList_normalHead hps
        let pN : NormalPrincipal := ⟨p, hpNormal⟩
        have hpAcc : Acc NormalPrincipal_lt pN :=
          NormalPrincipal_all_acc pN
        have hpsAcc : Acc NormalPrincipalList_lt ⟨p :: pList, hps⟩ :=
          NormalPrincipalList_acc hps hpAcc
        exact NormalCountableOrd_acc hpsAcc
  termination_by 10 * countableOrd_cmplx a.1 + 9
  decreasing_by
      all_goals
      subst_vars
      simp_all [countableOrd_cmplx, principalList_cmplx, principal_cmplx] <;> omega


theorem NormalPrincipal_all_acc (p : NormalPrincipal) : Acc NormalPrincipal_lt p := by
  rcases p with ⟨p,hp⟩
  cases p with
  | psi o =>
    cases hp with
    | psi ho hcoeff =>
      let oN : NormalOmegaTerm := ⟨o, ho⟩
      have hoAcc : Acc NormalOmegaTerm_lt oN :=
        NormalOmegaTerm_all_acc oN
      let motive : (a : NormalOmegaTerm) → Acc NormalOmegaTerm_lt a → Prop :=
        fun a _ =>
          ∀ haCoeff : coefficientList_lt
              (omegaTerm.coefficients a.1)
              (countableOrd.ofPrincipal (.psi a.1)),
            Acc NormalPrincipal_lt
              ⟨.psi a.1, principal_normal.psi a.2 haCoeff⟩
      exact Acc.rec (motive := motive)
        (fun a hpred ih haCoeff =>
          NormalPrincipal_acc_step a hpred ih haCoeff)
        hoAcc hcoeff
  termination_by 10 * principal_cmplx p.1 + 9
  decreasing_by
    all_goals
      subst_vars
      simp only [principal_cmplx]
      omega

theorem NormalOmegaTerm_all_acc (o : NormalOmegaTerm) : Acc NormalOmegaTerm_lt o := by
  rcases o with ⟨o, ho⟩
  cases o with
  | zero => exact NormalOmegaTerm_zero_acc
  | omegaNF alpha beta gamma =>
      have hAlphaNormal : omegaTerm_normal alpha :=
        omegaTerm_normal_alpha ho
      have hBetaNormal : countableOrd_normal beta :=
        omegaTerm_normal_beta ho
      have hGammaNormal : omegaTerm_normal gamma :=
        omegaTerm_normal_gamma ho
      let alphaN : NormalOmegaTerm := ⟨alpha, hAlphaNormal⟩
      let betaN : NormalCountableOrd := ⟨beta, hBetaNormal⟩
      let gammaN : NormalOmegaTerm := ⟨gamma, hGammaNormal⟩
      have hAlphaAcc : Acc NormalOmegaTerm_lt alphaN := NormalOmegaTerm_all_acc alphaN
      let motive : (a : NormalOmegaTerm) → Acc NormalOmegaTerm_lt a → Prop :=
        fun a _ =>
          ∀ (b : NormalCountableOrd) (g : NormalOmegaTerm)
            (h : omegaTerm_normal (.omegaNF a.1 b.1 g.1)),
            Acc NormalOmegaTerm_lt ⟨.omegaNF a.1 b.1 g.1, h⟩
      exact Acc.rec (motive := motive)
        (fun a hpred ih b g h =>
          NormalOmegaTerm_omegaNF_step a hpred ih b g h)
        hAlphaAcc betaN gammaN ho
  termination_by 10 * omegaTerm_cmplx o.1 + 9
  decreasing_by
    all_goals
      subst_vars
      simp only [omegaTerm_cmplx]
      omega

/-
If the normal omega-term o is accessible, and its coefficients are all smaller than the
principal term ψ(o), then the normal principal term ψ(o) is also accessible.
-/
theorem NormalPrincipal_acc_step
    (o : NormalOmegaTerm)
    (hpred : ∀ a, NormalOmegaTerm_lt a o → Acc NormalOmegaTerm_lt a)
    (ih :
      ∀ a, (ha : NormalOmegaTerm_lt a o) →
        (haCoeff : coefficientList_lt
          (omegaTerm.coefficients a.1)
          (countableOrd.ofPrincipal (.psi a.1))) →
        Acc NormalPrincipal_lt
          ⟨.psi a.1,
            principal_normal.psi a.2 haCoeff⟩)
    (hcoeff :
      coefficientList_lt
        (omegaTerm.coefficients o.1)
        (countableOrd.ofPrincipal (.psi o.1))) :
    Acc NormalPrincipal_lt
      ⟨.psi o.1,
        principal_normal.psi o.2 hcoeff⟩ := by
      apply Acc.intro

      rintro ⟨q, hqNormal⟩ hq

      cases q with
      | psi a =>
          cases hqNormal with
          | psi haNormal haCoeff =>

              cases hq with

              --------------------------------------------------
              -- ψ(a) < ψ(o), with a < o
              --------------------------------------------------
              | psi_forward harg _ =>
                  let aN : NormalOmegaTerm :=
                    ⟨a, haNormal⟩

                  exact ih aN harg haCoeff


              --------------------------------------------------
              -- reverse strict:
              -- ψ(a) < c, c ∈ coefficients(o)
              --------------------------------------------------
              | @psi_reverse_lt _ _ c hrev hc hltc =>
                  have hcNormal :
                      countableOrd_normal c :=
                    coefficient_normal_of_mem o.2 hc

                  let cN : NormalCountableOrd :=
                    ⟨c, hcNormal⟩

                  have hcAcc :
                      Acc NormalCountableOrd_lt cN :=
                    NormalCountableOrd_all_acc cN

                  let qN : NormalPrincipal :=
                    ⟨.psi a,
                      principal_normal.psi
                        haNormal
                        haCoeff⟩

                  let qC : NormalCountableOrd :=
                    ⟨countableOrd.ofPrincipal (.psi a),
                      countableOrd_ofPrincipal_normal qN.2⟩

                  have hqCAcc :
                      Acc NormalCountableOrd_lt qC :=
                    hcAcc.inv hltc

                  exact
                    NormalPrincipal_acc_of_ofPrincipal_acc
                      qN
                      hqCAcc


              --------------------------------------------------
              -- reverse equality:
              -- ψ(a) = c, c ∈ coefficients(o)
              --------------------------------------------------
              | @psi_reverse_eq _ _ c hrev hc heqc =>
                  have hcNormal :
                      countableOrd_normal c :=
                    coefficient_normal_of_mem o.2 hc

                  let cN : NormalCountableOrd :=
                    ⟨c, hcNormal⟩

                  have hcAcc :
                      Acc NormalCountableOrd_lt cN :=
                    NormalCountableOrd_all_acc cN

                  let qN : NormalPrincipal :=
                    ⟨.psi a,
                      principal_normal.psi
                        haNormal
                        haCoeff⟩

                  let qC : NormalCountableOrd :=
                    ⟨countableOrd.ofPrincipal (.psi a),
                      countableOrd_ofPrincipal_normal qN.2⟩

                  have hqCAcc :
                      Acc NormalCountableOrd_lt qC := by
                    apply NormalCountableOrd_acc_of_eq hcAcc
                    exact countableOrd_eq_sym heqc

                  exact
                    NormalPrincipal_acc_of_ofPrincipal_acc
                      qN
                      hqCAcc

  termination_by
    10 * principal_cmplx (.psi o.1) + 5

  decreasing_by
    all_goals
      subst_vars
      try have hc_cmplx := coefficient_cmplx_lt_of_mem hc
      simp only [principal_cmplx]
      omega


/-
Helper for omegaNF.

This is the lexicographic accessibility argument.

We successively induct on accessibility of:

  α
  β
  γ

so that:

  smaller exponent    -> use α induction hypothesis
  equal exponent,
  smaller coefficient -> use β induction hypothesis
  equal α and β,
  smaller remainder   -> use γ induction hypothesis

The custom equality cases are transported with
NormalOmegaTerm_acc_of_eq.
-/
theorem NormalOmegaTerm_omegaNF_step
    (alpha : NormalOmegaTerm)
    (hAlphaPred : ∀ a, NormalOmegaTerm_lt a alpha → Acc NormalOmegaTerm_lt a)
    (ihAlpha :
      ∀ a, (ha : NormalOmegaTerm_lt a alpha) →
        ∀ (b : NormalCountableOrd) (c : NormalOmegaTerm)
          (h : omegaTerm_normal (.omegaNF a.1 b.1 c.1)),
          Acc NormalOmegaTerm_lt ⟨.omegaNF a.1 b.1 c.1, h⟩)
    (beta : NormalCountableOrd)
    (gamma : NormalOmegaTerm)
    (hnormal :
      omegaTerm_normal
        (.omegaNF alpha.1 beta.1 gamma.1)) :
    Acc NormalOmegaTerm_lt
      ⟨.omegaNF alpha.1 beta.1 gamma.1,
        hnormal⟩ := by
  have hBetaAcc : Acc NormalCountableOrd_lt beta :=
    NormalCountableOrd_all_acc beta

      ----------------------------------------------------------
      -- Second coordinate: coefficient
      ----------------------------------------------------------
      revert gamma

      induction hBetaAcc with
      | intro beta hBetaPred ihBeta =>
          intro gamma hnormal

          ------------------------------------------------------
          -- Third coordinate: remainder
          ------------------------------------------------------
          have hGammaAcc : Acc NormalOmegaTerm_lt gamma :=
            NormalOmegaTerm_all_acc gamma
          revert hnormal

          induction hGammaAcc with
          | intro gamma hGammaPred ihGamma =>
              intro hnormal

              have hBetaPos :
                  countableOrd.zero <c beta.1 := by
                cases hnormal with
                | omegaNF _ _ _ hpos _ =>
                    exact hpos

              apply Acc.intro

              rintro ⟨x, hxNormal⟩ hxlt

              cases x with

              --------------------------------------------------
              -- zero < every omegaNF
              --------------------------------------------------
              | zero =>
                  exact NormalOmegaTerm_zero_acc


              | omegaNF a b c =>

                  have haNormal :
                      omegaTerm_normal a :=
                    omegaTerm_normal_alpha hxNormal

                  have hbNormal :
                      countableOrd_normal b :=
                    omegaTerm_normal_beta hxNormal

                  have hcNormal :
                      omegaTerm_normal c :=
                    omegaTerm_normal_gamma hxNormal

                  have hbPos :
                      countableOrd.zero <c b := by
                    cases hxNormal with
                    | omegaNF _ _ _ hpos _ =>
                        exact hpos

                  have hcBound :
                      c <o
                        .omegaNF
                          a
                          countableOrd.one
                          omegaTerm.zero := by
                    cases hxNormal with
                    | omegaNF _ _ _ _ hbound =>
                        exact hbound

                  let aN : NormalOmegaTerm :=
                    ⟨a, haNormal⟩

                  let bN : NormalCountableOrd :=
                    ⟨b, hbNormal⟩

                  let cN : NormalOmegaTerm :=
                    ⟨c, hcNormal⟩

                  cases hxlt with

                  ------------------------------------------------
                  -- a < alpha
                  ------------------------------------------------
                  | exponent hA =>
                      exact
                        ihAlpha
                          aN
                          hA
                          bN
                          cN
                          hxNormal


                  ------------------------------------------------
                  -- a = alpha and b < beta
                  ------------------------------------------------
                  | coefficient hAEq hB =>

                      have hOmegaEq :
                          (.omegaNF
                              a
                              countableOrd.one
                              omegaTerm.zero)
                            =o
                          (.omegaNF
                              alpha.1
                              countableOrd.one
                              omegaTerm.zero) := by
                        exact omegaTerm_eq.omegaNF
                          hAEq
                          (countableOrd_eq_refl
                            countableOrd.one)
                          omegaTerm_eq.zero

                      have hcBound' :
                          c <o
                            .omegaNF
                              alpha.1
                              countableOrd.one
                              omegaTerm.zero :=
                        omegaTerm_lt_eq_trans
                          hcBound
                          hOmegaEq

                      have hCanonNormal :
                          omegaTerm_normal
                            (.omegaNF
                              alpha.1
                              b
                              c) := by
                        exact omegaTerm_normal.omegaNF
                          alpha.2
                          hbNormal
                          hcNormal
                          hbPos
                          hcBound'

                      have hCanonAcc :
                          Acc NormalOmegaTerm_lt
                            ⟨.omegaNF alpha.1 b c,
                              hCanonNormal⟩ :=
                        ihBeta
                          bN
                          hB
                          cN
                          hCanonNormal

                      have hActualCanon :
                          (.omegaNF a b c)
                            =o
                          (.omegaNF alpha.1 b c) := by
                        exact omegaTerm_eq.omegaNF
                          hAEq
                          (countableOrd_eq_refl b)
                          (omegaTerm_eq_refl c)

                      apply
                        NormalOmegaTerm_acc_of_eq
                          hCanonAcc

                      exact
                        omegaTerm_eq_sym
                          hActualCanon


                  ------------------------------------------------
                  -- a = alpha, b = beta, c < gamma
                  ------------------------------------------------
                  | remainder hAEq hBEq hC =>

                      have hOmegaEq :
                          (.omegaNF
                              a
                              countableOrd.one
                              omegaTerm.zero)
                            =o
                          (.omegaNF
                              alpha.1
                              countableOrd.one
                              omegaTerm.zero) := by
                        exact omegaTerm_eq.omegaNF
                          hAEq
                          (countableOrd_eq_refl
                            countableOrd.one)
                          omegaTerm_eq.zero

                      have hcBound' :
                          c <o
                            .omegaNF
                              alpha.1
                              countableOrd.one
                              omegaTerm.zero :=
                        omegaTerm_lt_eq_trans
                          hcBound
                          hOmegaEq

                      have hCanonNormal :
                          omegaTerm_normal
                            (.omegaNF
                              alpha.1
                              beta.1
                              c) := by
                        exact omegaTerm_normal.omegaNF
                          alpha.2
                          beta.2
                          hcNormal
                          hBetaPos
                          hcBound'

                      have hCanonAcc :
                          Acc NormalOmegaTerm_lt
                            ⟨.omegaNF
                                alpha.1
                                beta.1
                                c,
                              hCanonNormal⟩ :=
                        ihGamma
                          cN
                          hC
                          hCanonNormal

                      have hActualCanon :
                          (.omegaNF a b c)
                            =o
                          (.omegaNF
                              alpha.1
                              beta.1
                              c) := by
                        exact omegaTerm_eq.omegaNF
                          hAEq
                          hBEq
                          (omegaTerm_eq_refl c)

                      apply
                        NormalOmegaTerm_acc_of_eq
                          hCanonAcc

                      exact
                        omegaTerm_eq_sym
                          hActualCanon

  termination_by
    10 *
        omegaTerm_cmplx
          (.omegaNF
            alpha.1
            beta.1
            gamma.1)
      + 5

  decreasing_by
    all_goals
      subst_vars
      simp only [omegaTerm_cmplx]
      omega
end

theorem countableOrd_lt_wf : WellFounded NormalCountableOrd_lt := by sorry
