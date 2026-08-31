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
-- Defining Normality
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
-- Structural Complexity 1
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
theorem coefficientList_tri (cs : List countableOrd) (bound : countableOrd) :
        coefficientList_lt cs bound ∨ ∃ c, c ∈ cs ∧ (bound <c c ∨ bound =c c) := by
  cases cs with
  | nil => left; exact coefficientList_lt.nil
  | cons c cs =>
      cases countableOrd_tri bound c with
      | inl hbc => right; exact ⟨c, List.mem_cons_self, Or.inl hbc⟩
      | inr hrest =>
          cases hrest with
          | inl heq => right; exact ⟨c, List.mem_cons_self, Or.inr heq⟩
          | inr hcb =>
              cases coefficientList_tri cs bound with
              | inl htail => left; exact coefficientList_lt.cons hcb htail
              | inr hexists =>
                  cases hexists with
                  | intro d hd =>
                      cases hd with
                      | intro hd_mem hd_rel =>
                          right
                          exact ⟨d, List.mem_cons_of_mem c hd_mem, hd_rel⟩
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
      simp [omegaTerm_cmplx]; omega

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
  simp [countableOrd.ofPrincipal, countableOrd_cmplx, principalList_cmplx,
        principal_cmplx]

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
      try simp [countableOrd_cmplx]
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
-- Defining Normal Objects
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
-- Properties of Normal Objects
--===============================================================================
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


--==================================================================================================
def principalList_bounded_by (p : principal) (ps : List principal) : Prop :=
  ∀ q, q ∈ ps → q ≤p p
-- NormalPrincipalList.nil is accessible
theorem NormalPrincipalList_nil_acc :
        Acc NormalPrincipalList_lt ⟨[], principalList_normal.nil⟩ := by
  apply Acc.intro
  -- ∀ n : NPL, n <npl ⟨[], principalList_normal.nil⟩ → Acc NPL_lt n
  rintro ⟨ps, hps⟩ hlt
  change principalList_lt ps [] at hlt
  cases hlt
-- Normal Principal is accessible with respect to equality
theorem NormalPrincipal_acc_of_eq
        {p q : NormalPrincipal} (hp : Acc NormalPrincipal_lt p) (hpq : p=npq) :
        Acc NormalPrincipal_lt q := by
  apply Acc.intro -- ∀r<npq, Acc NormalPrincipal_lt r
  intro r hrq
  apply hp.inv
  exact principal_lt_eq_trans hrq (principal_eq_sym hpq)
-- NormalPrincipalList.cons is accessible with certain conditions
theorem NormalPrincipalList_cons_acc (p : NormalPrincipal) (hp : Acc NormalPrincipal_lt p)
        (hsmall : ∀ q : NormalPrincipal, q <np p →
                  ∀ qs : NormalPrincipalList, principalList_bounded_by q.1 qs.1 →
                  Acc NormalPrincipalList_lt qs)
        (ps : NormalPrincipalList) (hps : Acc NormalPrincipalList_lt ps)
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
-- If a NormalPrincipalList ps is bounded above by an accessible NormalPrincipal p,
-- then ps is accessible
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
-- NormalPrincipalList is accessible
theorem NormalPrincipalList_acc_of_lt {pl1 pl2 : NormalPrincipalList}
        (h1 : Acc NormalPrincipalList_lt pl1) (h21 : NormalPrincipalList_lt pl2 pl1) :
        Acc NormalPrincipalList_lt pl2 :=
  h1.inv h21
/- If the head of a NormalPrincipalList is accessible, then the whole NormalPrincipalList
   is accessible -/
theorem NormalPrincipalList_acc {p : principal} {ps : List principal}
    (hnormal : principalList_normal (p :: ps))
    (hp :
      Acc NormalPrincipal_lt
        ⟨p, NormalPrincipalList_normalHead hnormal⟩) :
    Acc NormalPrincipalList_lt ⟨p :: ps, hnormal⟩ := by
  let pnormal : NormalPrincipal :=
    ⟨p, NormalPrincipalList_normalHead hnormal⟩
  apply NormalPrincipalList_acc_of_bound_acc
    pnormal hp ⟨p :: ps, hnormal⟩
  intro q hq
  simp only [List.mem_cons] at hq
  rcases hq with hqp | hq
  · subst q
    exact Or.inr (principal_eq_refl p)
  · exact principalList_normal_tail_bounded hnormal q hq
/- If a NormalPrincipalList is accessible, then the corresponding NormalCountableOrd is
   accessible -/
theorem NormalCountableOrd_acc_of_list_acc
    {ps : NormalPrincipalList}
    (hps : Acc NormalPrincipalList_lt ps) :
    Acc NormalCountableOrd_lt
      ⟨countableOrd.sum ps.1,
       countableOrd_normal.sum ps.2⟩ := by
  induction hps with
  | intro ps hpred ih =>
      apply Acc.intro
      rintro ⟨a, ha⟩ hlt
      cases a with
      | sum qs =>
          cases ha with
          | sum hqsNormal =>
              cases hlt with
              | sum hqsLt =>
                  exact ih ⟨qs, hqsNormal⟩ hqsLt
-- If some NormalCountableOrd a is accesible and b < a, then b is accessible
theorem NormalCountableOrd_acc_of_lt {a b : NormalCountableOrd}
        (ha : Acc NormalCountableOrd_lt a) (hba : b <nc a) :
        Acc NormalCountableOrd_lt b :=
  ha.inv hba
-- If NormalPrincipal_lt relation is well-founded, then normalPrincipalList is accessible
theorem NormalPrincipalList_all_acc_of_principal_wf
    (hP : WellFounded NormalPrincipal_lt)
    (ps : NormalPrincipalList) :
    Acc NormalPrincipalList_lt ps := by
  rcases ps with ⟨ps, hps⟩
  cases ps with
  | nil => exact NormalPrincipalList_nil_acc
  | cons p ps =>
    have hp : Acc NormalPrincipal_lt ⟨p, NormalPrincipalList_normalHead hps⟩ := by
      exact hP.apply ⟨p, NormalPrincipalList_normalHead hps⟩
    exact NormalPrincipalList_acc hps hp
-- If NormalPrincipal_lt relation is well-founded, then NormalCountableOrd is accessible
theorem NormalCountableOrd_all_acc_of_principal_wf
    (hP : WellFounded NormalPrincipal_lt)
    (a : NormalCountableOrd) :
    Acc NormalCountableOrd_lt a := by
  rcases a with ⟨a, ha⟩
  cases a with
  | sum ps =>
      cases ha with
      | sum hps =>
          let psN : NormalPrincipalList := ⟨ps, hps⟩
          have hpsAcc : Acc NormalPrincipalList_lt psN :=
            NormalPrincipalList_all_acc_of_principal_wf hP psN
          exact NormalCountableOrd_acc_of_list_acc hpsAcc
-- If NormalPrincipal_lt relation is well-founded, then NormalCountableOrd_lt relation is
-- well-founded
theorem NormalCountableOrd_lt_wf_of_principal_wf
    (hP : WellFounded NormalPrincipal_lt) :
    WellFounded NormalCountableOrd_lt := by
  constructor
  intro a
  exact NormalCountableOrd_all_acc_of_principal_wf hP a
/-
    1. Tree
        ↓
    2. NormalPrincipal_lt is well-founded
        ↓  (NormalPrincipalList_all_acc_of_principal_wf)
    3. NormalPrincipalList_lt is well-founded
        ↓  (NormalCountableOrd_all_acc_of_principal_wf)
    4. NormalCountableOrd_lt is well-founded
-/
--========================================================================================
-- Gap tree (Two-labelled trees with the strong gap condition)
--========================================================================================
/- We employ the proof method introduced by Anton Freund in https://arxiv.org/abs/2105.09915.
   · Definition
   Given an arbitrary partial order X and natural number N, he denotes T_N(X) as finite rooted
   trees. Internal nodes carry labels 0,⋯,N−1. He writes nodes as n ⋆ [t₀, t₁, ... t_{k-1}] where
   the brakets are finite "multisets." Multiset is multiset is a finite collection with
   multiplicity, equivalently a finite sequence modulo reordering. So, [A, B] = [B, A].
   · Comparison
   Suppose σ = [s₀, s₁, ..., s_{k-1}] and τ = [t₀, t₁, ..., t_{m-1}]. Given some relation ≤ between
   trees, he defines σ ≤^M τ to mean that there is an injection f : {0, ..., k-1} → {0, ..., m-1}
   such that s_i ≤ t_{f(i)} for every i < k. Freund uses T₂(∅) for the case of BH ordinals. There
   are two possibilities Freund notes: given s = m ⋆ σ and t = n ⋆ τ
   (i) m = n and σ ≤^M τ
   So, if we have σ = [A, B, C] and τ = [W, X, Y, Z], source branches can be injectively distributed
   among target branches. So, for example, A ↦ Y, B ↦ W, C ↦ Z
   (ii) m < n
   Denoting t = n ⋆ [t₀, t₁, ..., t_{m-1}], s ≤ t if s ≤ tᵢ for some i provided r(s) ≤ n where r(s)
   denotes the label at the root of s. So, if we have have t = n ⋆ [A, B, C], the whole s is in B.
   He calls this the "strong gap condition".

-/
--========================================================================================
-- Definition

-- The two labels 0 and 1 used in T₂(∅)
abbrev GapLabel := Fin 2
/- A finite rooted tree whose nodes are labelled by 0 or 1. The List is only a concrete storage
   representation of the finite collection of children. The embedding relation below will NOT
   depend on their left-to-right positions. -/
inductive GapTree where
  | node : GapLabel → List GapTree → GapTree
namespace GapTree
-- Retrieve root node from GapTree
def rootLabel : GapTree → GapLabel
  | .node n _ => n
-- Retrieve the immediate subtree of GapTree
def children : GapTree → List GapTree
  | .node _ ts => ts

@[simp]
theorem rootLabel_node (n : GapLabel) (ts : List GapTree) :
        rootLabel (.node n ts) = n := rfl
@[simp]
theorem children_node (n : GapLabel) (ts : List GapTree) :
        children (.node n ts) = ts := rfl
end GapTree

--========================================================================================
-- Embedding

mutual
-- GapTreeEmbeds s t to mean s embeds into t with the "strong gap condition"
inductive GapTreeEmbeds : GapTree → GapTree → Prop where
  | root {n : GapLabel} {ss ts : List GapTree} (h : GapForestEmbeds ss ts) :
    GapTreeEmbeds (.node n ss) (.node n ts)
  | descend {s t : GapTree} {n : GapLabel} {before after : List GapTree}
            (hlabel : GapTree.rootLabel s ≤ n) (h : GapTreeEmbeds s t) :
    GapTreeEmbeds s (.node n (before ++ t :: after))
-- GapForestEmbeds ss ts means all trees in ss can be matched injectively with distinct trees in ts
inductive GapForestEmbeds : List GapTree → List GapTree → Prop where
  | nil {ts : List GapTree} : GapForestEmbeds [] ts
  | cons {s t : GapTree} {ss before after : List GapTree} (hst : GapTreeEmbeds s t)
         (hrest : GapForestEmbeds ss (before ++ after)) :
         GapForestEmbeds (s :: ss) (before ++ (t :: after))
end

-- Reflexitivity

mutual
theorem GapTreeEmbeds_refl (t : GapTree) : GapTreeEmbeds t t := by
  cases t with
  | node n list =>
    apply GapTreeEmbeds.root --newgoal: GapForestEmbeds list list
    exact GapForestEmbeds_refl list
theorem GapForestEmbeds_refl (ts : List GapTree) : GapForestEmbeds ts ts := by
  cases ts with
  | nil => exact GapForestEmbeds.nil
  | cons t ts =>
    have ht : GapTreeEmbeds t t := GapTreeEmbeds_refl t
    have hts : GapForestEmbeds ts ts := GapForestEmbeds_refl ts
    simpa using (GapForestEmbeds.cons (s := t) (t := t) (ss := ts) (before := [])
                                      (after := ts) ht hts)
end

-- Append

/- Suppose a target node contains s as one of its children and (rootLabel of s) ≤ n, then
   s should embed into that parent node. -/
theorem GapTreeEmbeds_into_parent {s : GapTree} {n : GapLabel} {before after : List GapTree}
        (hlabel : GapTree.rootLabel s ≤ n) :
        GapTreeEmbeds s (.node n (before ++ (s :: after))) := by
  apply GapTreeEmbeds.descend
  · exact hlabel
  · exact GapTreeEmbeds_refl s
-- σ ≤M τ → σ ≤M [u] ∪ τ
theorem GapForestEmbeds_weaken_cons {ss ts : List GapTree} (h : GapForestEmbeds ss ts)
        (u : GapTree) : GapForestEmbeds ss (u :: ts) := by
  cases h with
  | nil => exact GapForestEmbeds.nil
  | @cons s t ss before after hst hrest =>
      apply GapForestEmbeds.cons (s := s) (t := t) (ss := ss) (before := u :: before)
                                 (after := after)
      · exact hst
      · simpa using GapForestEmbeds_weaken_cons hrest u
-- σ ≤M τ → σ ≤M us ∪ τ
theorem GapForestEmbeds_weaken_prefix {ss ts : List GapTree} (h : GapForestEmbeds ss ts)
        (us : List GapTree) : GapForestEmbeds ss (us ++ ts) := by
  induction us with
  | nil => simpa using h
  | cons u us ih => simpa using GapForestEmbeds_weaken_cons ih u
-- σ ≤M τ → σ ≤M τ ∪ us
theorem GapForestEmbeds_weaken_suffix {ss ts : List GapTree} (h : GapForestEmbeds ss ts)
        (us : List GapTree) : GapForestEmbeds ss (ts ++ us) := by
  cases h with
  | nil => exact GapForestEmbeds.nil
  | @cons s t ss before after hst hrest =>
    have hrest' : GapForestEmbeds ss (before ++ (after ++ us)) := by
      simpa [List.append_assoc] using GapForestEmbeds_weaken_suffix hrest us
    have hcons : GapForestEmbeds (s :: ss) (before ++ (t :: (after ++ us))) := by
        exact GapForestEmbeds.cons (s := s) (t := t) (ss := ss) (before := before)
              (after := after ++ us) hst hrest'
    simpa [List.append_assoc] using hcons
/- If ss embeds into ts, then it still embeds after adding arbitrary unused target children
   before and after ts. σ ≤M τ → σ ≤M (ρ + τ + η)-/
theorem GapForestEmbeds_weaken {ss ts : List GapTree} (h : GapForestEmbeds ss ts)
        (before after : List GapTree) : GapForestEmbeds ss (before ++ ts ++ after) := by
  have hprefix : GapForestEmbeds ss (before ++ ts) := GapForestEmbeds_weaken_prefix h before
  exact GapForestEmbeds_weaken_suffix hprefix after

-- Embedding properties

-- If s embeds into t, then the root label of s is ≤ the root label of t
theorem GapTreeEmbeds_rootLabel_le {s t : GapTree} (h : GapTreeEmbeds s t) :
        GapTree.rootLabel s ≤ GapTree.rootLabel t := by
  cases h with
  | root h => exact le_rfl
  | descend hlabel h => exact hlabel
/- if a source tree occurs in a forest that embeds into another forest,
   then it embeds into some tree in the target forest. -/
theorem GapForestEmbeds_exists_of_mem {ss ts : List GapTree} (h : GapForestEmbeds ss ts)
        {s : GapTree} (hs : s ∈ ss) : ∃ t, t ∈ ts ∧ GapTreeEmbeds s t := by
  cases h with
  | nil => simp at hs
  | @cons s₀ t₀ ss before after hst hrest =>
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · refine ⟨t₀, ?_, hst⟩
        simp
      · obtain ⟨t, ht, hst'⟩ :=
          GapForestEmbeds_exists_of_mem hrest hs
        refine ⟨t, ?_, hst'⟩
        simp only [List.mem_append, List.mem_cons] at ht ⊢
        rcases ht with ht | ht
        · exact Or.inl ht
        · exact Or.inr (Or.inr ht)
/- If s :: ss is embedded in ts, then there exist t (child of ts), before and after
   such that s ∈ t, ts = before ∪ t ∪ after, and ss ∈ before ∪ after -/
theorem GapForestEmbeds_head {s : GapTree} {ss ts : List GapTree}
        (h : GapForestEmbeds (s :: ss) ts) :
        ∃ t before after, ts = before ++ (t :: after) ∧ GapTreeEmbeds s t ∧
        GapForestEmbeds ss (before ++ after) := by
  cases h with
  | @cons s t ss before after hst hrest =>
      exact ⟨t, before, after, rfl, hst, hrest⟩

--========================================================================================
-- Two-labeled Trees

namespace GapTree
def label0 : GapLabel := ⟨0, by omega⟩
def label1 : GapLabel := ⟨1, by omega⟩
def node0 (ts : List GapTree) : GapTree := .node label0 ts
def node1 (ts : List GapTree) : GapTree := .node label1 ts
/- Freund uses the following constructor to represent collapsed terms
   f(ϑα)=0⋆[1⋆[f(α)]]. -/
/-                  0
                    |
                    1
                    |
                some tree                                       -/
def collapseWrap (t : GapTree) : GapTree := node0 [node1 [t]]
@[simp]
theorem GapTree_rootLabel_node0 (ts : List GapTree) :
        GapTree.rootLabel (GapTree.node0 ts) = GapTree.label0 := rfl
@[simp]
theorem GapTree_rootLabel_node1 (ts : List GapTree) :
        GapTree.rootLabel (GapTree.node1 ts) = GapTree.label1 := rfl
@[simp]
theorem GapTree_rootLabel_collapseWrap (t : GapTree) :
        GapTree.rootLabel (GapTree.collapseWrap t) = GapTree.label0 := rfl
end GapTree

-- E-bar function
/- As mentioned before, Freund encodes the collapsed terms as
   f(ϑ(α)) = [0 ⋆ [1 ⋆ f(α)]] where θ is the collapsing function. The E-bar function
   scans a tree t and extracts the subtrees that look like encodings of collapsed ϑ-terms.
   -/
namespace GapTree
mutual
def Ebar (t : GapTree) : List GapTree :=
  match t with
  | .node n ts =>
    if n = label0 ∧ ∃ u ∈ ts, rootLabel u = label1 then
      [t]
    else EbarForest ts
def EbarForest (ts : List GapTree) : List GapTree :=
  match ts with
    | [] => []
    | t :: ts => Ebar t ++ EbarForest ts
end
-- Ebar to an actual collapse wrapper returns that whole wrapper
@[simp]
theorem Ebar_collapseWrap (t : GapTree) : GapTree.Ebar (GapTree.collapseWrap t) =
        [GapTree.collapseWrap t] := by
  simp [GapTree.Ebar, GapTree.collapseWrap, GapTree.node0, GapTree.node1,
        GapTree.rootLabel]
end GapTree
-- Every tree returned by Ebar has root label 0.
mutual
theorem Ebar_mem_rootLabel_eq_label0 {s t : GapTree} (hs : s ∈ GapTree.Ebar t) :
        GapTree.rootLabel s = GapTree.label0 := by
  cases t with
  | node n ts =>
    rw [GapTree.Ebar] at hs
    /- given (t=.node n ts)
       hs : s ∈ (if n = label0 ∧ ∃u ∈ ts, rootLabel u = label1 then [t] else EbarForest ts) -/
    split at hs
    -- if n = label0 ∧ ∃u ∈ ts, rootLabel u = label1 then [t]
    next h1 => simp at hs
               subst s
               exact h1.1
    next h2 => exact EbarForest_mem_rootLabel_eq_label0 hs
theorem EbarForest_mem_rootLabel_eq_label0 {s : GapTree} {ts : List GapTree}
        (hs : s ∈ GapTree.EbarForest ts) :
        GapTree.rootLabel s = GapTree.label0 := by
  cases ts with
  | nil => simp [GapTree.EbarForest] at hs
  | cons t ts =>
      rw [GapTree.EbarForest] at hs
      simp only [List.mem_append] at hs
      rcases hs with hs | hs
      · exact Ebar_mem_rootLabel_eq_label0 hs
      · exact EbarForest_mem_rootLabel_eq_label0 hs
end
theorem GapTree_label0_le (n : GapLabel) : GapTree.label0 ≤ n := by
  change 0 ≤ n.val
  omega
-- Every Ebar piece embeds into the tree it came from
mutual
theorem Ebar_mem_embeds {s t : GapTree} (hs : s ∈ GapTree.Ebar t) :
        GapTreeEmbeds s t := by
  cases t with
  | node n ts => rw [GapTree.Ebar] at hs
                 split at hs -- if n = label0 ∧ ∃u ∈ ts, rootLabel u = label1 then [t]
                 next h1 => simp at hs
                            subst s
                            exact GapTreeEmbeds_refl (.node n ts)
                 next h2 => obtain ⟨u, before, after, hts, hsu⟩ :=
                              EbarForest_mem_exists_embeds hs
                            rw [hts]
                            apply GapTreeEmbeds.descend
                            · calc GapTree.rootLabel s = GapTree.label0 :=
                                    EbarForest_mem_rootLabel_eq_label0 hs
                                  _ ≤ n := GapTree_label0_le n
                            · exact hsu
theorem EbarForest_mem_exists_embeds {s : GapTree} {ts : List GapTree}
        (hs : s ∈ GapTree.EbarForest ts) :
        ∃ u before after, ts = before ++ (u :: after) ∧ GapTreeEmbeds s u := by
  cases ts with
  | nil => simp [GapTree.EbarForest] at hs
  | cons t ts => rw [GapTree.EbarForest] at hs
                 simp only [List.mem_append] at hs
                 rcases hs with hTree | hForest
                 · refine ⟨t, [], ts, ?_, Ebar_mem_embeds hTree⟩; simp
                 · obtain ⟨u, before, after, hts, hsu⟩ :=
                    EbarForest_mem_exists_embeds hForest
                   refine ⟨u, t :: before, after, ?_, hsu⟩; simp [hts]
end
-- 0 ≤ n ≤ 1
theorem GapTree_le_label1 (n : GapLabel) : n ≤ GapTree.label1 := by
  change n.val ≤ 1; omega
-- if t ∈ ts and s ∈ Ebar(t) then s ∈ EBar_forest​(ts).
theorem Ebar_mem_EbarForest_of_mem {s t : GapTree} {ts : List GapTree}
        (ht : t ∈ ts) (hs : s ∈ GapTree.Ebar t) : s ∈ GapTree.EbarForest ts := by
  induction ts with
  | nil =>
      simp at ht
  | cons u us ih =>
      rw [GapTree.EbarForest]
      simp only [List.mem_append]
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact Or.inl hs
      · exact Or.inr (ih ht)
/- If a collapse-shaped tree embeds into t, then it already embeds into some
   critical piece returned (Freund's naming of the first appearence of the callapse-
   shaped tree in a given tree) by Ebar t. -/
theorem collapseWrap_embeds_Ebar {s t : GapTree} (h : GapTreeEmbeds (GapTree.collapseWrap s) t) :
        ∃ u, u ∈ GapTree.Ebar t ∧ GapTreeEmbeds (GapTree.collapseWrap s) u := by
  -- node0 [node1 [t]]
  unfold GapTree.collapseWrap GapTree.node0 GapTree.node1 at h
  cases h with
  | @root n ss ts hforest =>
    have hmem : (.node GapTree.label1 [s] : GapTree) ∈ [(.node GapTree.label1 [s] : GapTree)] := by
      simp
    obtain ⟨u, hu, h1u⟩ := GapForestEmbeds_exists_of_mem hforest hmem
    have hLower : GapTree.label1 ≤ GapTree.rootLabel u := by
      simpa using GapTreeEmbeds_rootLabel_le h1u
    have huLabel : GapTree.rootLabel u = GapTree.label1 := by
      apply le_antisymm
      · exact GapTree_le_label1 _
      · exact hLower
    refine ⟨.node GapTree.label0 ts, ?_, ?_⟩
    · have hcond :
          GapTree.label0 = GapTree.label0 ∧
            ∃ v ∈ ts, GapTree.rootLabel v = GapTree.label1 := by
          constructor
          · rfl
          · exact ⟨u, hu, huLabel⟩
      rw [GapTree.Ebar, if_pos hcond]
      simp
    · simpa [GapTree.collapseWrap, GapTree.node0, GapTree.node1] using GapTreeEmbeds.root hforest
  | @descend source t₀ n before after hlabel hsub =>
      obtain ⟨u, huEbar, huEmbed⟩ := collapseWrap_embeds_Ebar hsub
      by_cases hcrit : n = GapTree.label0 ∧ ∃ v ∈ before ++ (t₀ :: after),
                       GapTree.rootLabel v = GapTree.label1
      · refine ⟨.node n (before ++ (t₀ :: after)), ?_, ?_⟩
        · change
            (.node n (before ++ (t₀ :: after)) : GapTree) ∈
            (if n = GapTree.label0 ∧ ∃ v ∈ before ++ (t₀ :: after),
                GapTree.rootLabel v = GapTree.label1
             then [.node n (before ++ (t₀ :: after))]
             else GapTree.EbarForest (before ++ (t₀ :: after)))
          rw [if_pos hcrit]; simp
        · exact GapTreeEmbeds.descend hlabel hsub
      · refine ⟨u, ?_, huEmbed⟩
        change
          u ∈ (if n = GapTree.label0 ∧ ∃ v ∈ before ++ (t₀ :: after),
                  GapTree.rootLabel v = GapTree.label1
               then [.node n (before ++ (t₀ :: after))]
               else GapTree.EbarForest (before ++ (t₀ :: after)))
        rw [if_neg hcrit]
        apply Ebar_mem_EbarForest_of_mem
          (t := t₀)
          (ts := before ++ (t₀ :: after))
        · simp
        · exact huEbar
termination_by t
decreasing_by
  have hmem : t₀ ∈ before ++ (t₀ :: after) := by simp
  have hsize := List.sizeOf_lt_of_mem hmem
  simp_all
  omega

--========================================================================================
-- Encoding
--========================================================================================
/- We now encode our ordinal notations into this gap tree data type. But ours differ from
   Fruend's data type. We follow the following outline:
   1. Formalize Freunds term system as a small immediate datatype.
   2. Define its normality/order
   3. Define f : FreundTerm → GapTree
   4. Prove EBar(f(a)) ≃ E(a)
   5. Use collapseWrap_embeds_Ebar
   6. Prove f_order_reflecting
   7. Prove FreundTerm order well-founded
   8. Bridge our ψ/ΩNF notation to FreundTerm
   9. WellFounded NormalPrincipal_lt
   10. WellFounded NormalCountableOrd_lt
   * We mostly just follow Fruend's notations   -/
/- FreundTerm.Omega ↦ Ω
    f(Ω) = 1 ⋆ []
   FruendTerm.theta a ↦ ϑ(a)
    f(ϑa) = 0 ⋆ [1 ⋆ [f(a)]]
   FreundTerm.cnf [a₀, a₁, ..., a_{n-1}] ↦ ω^a₀ + ω^a₁ + ... + ω^{a_{n-1}}
    f(⟨a₀, a₁, ..., a_{n-1}⟩) = i ⋆ [f(a₀), ..., f(a_{n-1})] -/
inductive FreundTerm where
  | Omega : FreundTerm
  | theta : FreundTerm → FreundTerm
  | cnf   : List FreundTerm → FreundTerm
-- E Map (Critical-Term Function)
namespace FreundTerm
mutual
def E : FreundTerm → List FreundTerm
  | .Omega => []                                -- E(Ω) = []
  | .theta a => [.theta a]                      -- E(ϑ a) = [ϑ a]
  | .cnf as => EList as                         -- E(cnf [a₀, a₁, ..., a_{n-1}]) =
                                                --    E(a₀) ++ ... ++ E(a_{n-1})
def EList : List FreundTerm → List FreundTerm
  | [] => []
  | a :: as => E a ++ EList as
end
end FreundTerm

-- Comparison

mutual
inductive FreundTerm_lt : FreundTerm → FreundTerm → Prop where
  -- Ω < cnf(b :: bs) when Ω < b
  | Omega_cnf_lt {b : FreundTerm} {bs : List FreundTerm}
                (h : FreundTerm_lt .Omega b) :
      FreundTerm_lt .Omega (.cnf (b :: bs))
  -- Ω < cnf(Ω :: bs)
  | Omega_cnf_eq {bs : List FreundTerm} : FreundTerm_lt .Omega (.cnf (.Omega :: bs))
  -- θα < Ω
  | theta_Omega {a : FreundTerm} : FreundTerm_lt (.theta a) .Omega
  -- θα < cnf(b :: bs) when θα < b
  | theta_cnf_lt {a b : FreundTerm} {bs : List FreundTerm}
                 (h : FreundTerm_lt (.theta a) b) :
      FreundTerm_lt (.theta a) (.cnf (b :: bs))
  -- θα < cnf(θα :: bs)
  | theta_cnf_eq {a : FreundTerm} {bs : List FreundTerm} :
      FreundTerm_lt (.theta a) (.cnf (.theta a :: bs))
  -- α < β and every critical term of α is below θβ
  | theta_theta_forward {a b : FreundTerm} (hab : FreundTerm_lt a b)
                        (hE : ∀ g, g ∈ FreundTerm.E a → FreundTerm_lt g (.theta b)) :
      FreundTerm_lt (.theta a) (.theta b)
  -- θα < θβ because some g ∈ E(β) strictly dominates θα
  | theta_theta_support_lt {a b g : FreundTerm} (hg : g ∈ FreundTerm.E b)
                           (h : FreundTerm_lt (.theta a) g) :
      FreundTerm_lt (.theta a) (.theta b)
  -- θα < θβ because θα itself occurs in E(β)
  | theta_theta_support_eq {a b : FreundTerm} (hg : .theta a ∈ FreundTerm.E b) :
      FreundTerm_lt (.theta a) (.theta b)
  -- [] < Ω
  | cnf_nil_Omega : FreundTerm_lt (.cnf []) .Omega
  -- [] < θβ
  | cnf_nil_theta {b : FreundTerm} : FreundTerm_lt (.cnf []) (.theta b)
  -- cnf(a :: as) < Ω when a < Ω
  | cnf_Omega {a : FreundTerm} {as : List FreundTerm} (h : FreundTerm_lt a .Omega) :
      FreundTerm_lt (.cnf (a :: as)) .Omega
  -- cnf(a :: as) < θβ when a < θβ
  | cnf_theta {a b : FreundTerm} {as : List FreundTerm} (h : FreundTerm_lt a (.theta b)) :
      FreundTerm_lt (.cnf (a :: as)) (.theta b)
  -- lexicographic CNF comparison
  | cnf_cnf {as bs : List FreundTerm} (h : FreundTermList_lt as bs) :
      FreundTerm_lt (.cnf as) (.cnf bs)
inductive FreundTermList_lt : List FreundTerm → List FreundTerm → Prop where
  | nil {b : FreundTerm} {bs : List FreundTerm} :
      FreundTermList_lt [] (b :: bs)
  | head {a b : FreundTerm} {as bs : List FreundTerm} (h : FreundTerm_lt a b) :
      FreundTermList_lt (a :: as) (b :: bs)
  | tail {a : FreundTerm} {as bs : List FreundTerm} (h : FreundTermList_lt as bs) :
      FreundTermList_lt (a :: as) (a :: bs)
end
-- Weak Comparison
def FreundTerm_le (a b : FreundTerm) : Prop :=
  FreundTerm_lt a b ∨ a = b
infix:50 " <f " => FreundTerm_lt
infix:50 " ≤f " => FreundTerm_le

-- Normality
/- Freund imposes two conditions for the cnf
   1. if it has at least two entries, they must be non-increasing
   2. if it has exactly one entry [α], α cannot be Ω nor ϑ β for some β -/

def FreundSingletonOK : FreundTerm → Prop
  | .cnf _ => True
  | _ => False
mutual
inductive FreundTerm_normal : FreundTerm → Prop where
  | Omega : FreundTerm_normal .Omega
  | theta {a : FreundTerm} (ha : FreundTerm_normal a) : FreundTerm_normal (.theta a)
  | cnf {as : List FreundTerm} (has : FreundTermList_normal as)
        (hsingle : ∀ a, as = [a] → FreundSingletonOK a) :
      FreundTerm_normal (.cnf as)
inductive FreundTermList_normal : List FreundTerm → Prop where
  | nil : FreundTermList_normal []
  | single {a : FreundTerm} (ha : FreundTerm_normal a) :
      FreundTermList_normal [a]
  | cons {a b : FreundTerm} {rest : List FreundTerm} (ha : FreundTerm_normal a)
         (htail : FreundTermList_normal (b :: rest))
         (hbound : ∀ t, t ∈ (b :: rest) → t ≤f a) :
      FreundTermList_normal (a :: b :: rest)
end
def NormalFreundTerm := {a : FreundTerm // FreundTerm_normal a}

-- Encoding

namespace FreundTerm
/- Recall the encoding rule Freund defines. In short, for a cnf list, i = 0 if the list is empty
   or the head is <Ω and i = 1 otherwise. -/
noncomputable def cnfLabel (as : List FreundTerm) : GapLabel := by
  classical
  exact match as with
        | [] => GapTree.label0
        | a :: _ => if a <f .Omega then GapTree.label0
                    else GapTree.label1
mutual
noncomputable def tree : FreundTerm → GapTree
  | .Omega => GapTree.node1 []
  -- 1 (no children)
  | .theta a => GapTree.collapseWrap (tree a)
  /-     0
         |
         1
         |
      tree a     -/
  | .cnf as => .node (cnfLabel as) (treeList as)
  /- If as = [a b c]
              i
            / | \
  (tree a)(tree b)(tree c)      -/
noncomputable def treeList : List FreundTerm → List GapTree
  | [] => []
  | a :: as => tree a :: treeList as
end
end FreundTerm
-- Some properties
namespace FreundTerm
@[simp]
theorem tree_Omega : tree .Omega = GapTree.node1 [] := by rfl
@[simp]
theorem tree_theta (a : FreundTerm) : tree (.theta a) = GapTree.collapseWrap (tree a) := by rfl
@[simp]
theorem treeList_nil : treeList [] = [] := by rfl
@[simp]
theorem treeList_cons (a : FreundTerm) (as : List FreundTerm) :
        treeList (a :: as) = tree a :: treeList as := by rfl
@[simp]
theorem cnfLabel_nil : cnfLabel [] = GapTree.label0 := by rfl
@[simp]
theorem cnfLabel_cons_of_lt {a : FreundTerm} {as : List FreundTerm} (h : ¬ a <f .Omega) :
        cnfLabel (a :: as) = GapTree.label1 := by simp [cnfLabel, h]
-- If a < Ω, a can only have forms (1) theta x, (2) cnf [], or (3) cnf (x :: xs) where x <f Ω
theorem tree_rootLabel_eq_label0_of_lt_Omega {a : FreundTerm} (h : a <f .Omega) :
        GapTree.rootLabel (tree a) = GapTree.label0 := by
  cases h with
  | theta_Omega => simp
  | cnf_nil_Omega => change cnfLabel [] = GapTree.label0
                     exact cnfLabel_nil
  | cnf_Omega hhead => simp [tree, cnfLabel, hhead]
-- Opposite of above
theorem not_lt_Omega_of_tree_rootLabel_eq_label1 {a : FreundTerm}
    (hroot : GapTree.rootLabel (tree a) = GapTree.label1) : ¬ a <f .Omega := by
  intro hlt -- a <f .Omega
  have h0 : GapTree.rootLabel (tree a) = GapTree.label0 :=
    tree_rootLabel_eq_label0_of_lt_Omega hlt
  have h01 : GapTree.label0 = GapTree.label1 := by
    exact h0.symm.trans hroot
  have hv := congrArg Fin.val h01
  simp [GapTree.label0, GapTree.label1] at hv
-- All the tail components are less than head
theorem FreundTermList_normal_tail_bounded {a : FreundTerm} {as : List FreundTerm}
        (h : FreundTermList_normal (a :: as)) :
        ∀ t, t ∈ as → t ≤f a := by
  intro t ht
  cases as with
  | nil => simp at ht
  | cons b rest => cases h with
                   | cons ha htail hbound => exact hbound t ht
-- If the list (of cnf) is normal its head is normal
theorem FreundTermList_normal_head {a : FreundTerm} {as : List FreundTerm}
        (h : FreundTermList_normal (a :: as)) : FreundTerm_normal a := by
  cases as with
  | nil => cases h with
           | single ha => exact ha
  | cons b bs => cases h with
                 | cons ha htail hbound => exact ha
-- If the list (of cnf) is normal its tail is normal
theorem FreundTermList_normal_tail {a : FreundTerm} {as : List FreundTerm}
        (h : FreundTermList_normal (a :: as)) : FreundTermList_normal as := by
  cases as with
  | nil => exact FreundTermList_normal.nil
  | cons b bs => cases h with
                 | cons ha htail hbound => exact htail
-- A transparent syntax-node count used for well-founded recursion below.
mutual
def complexity : FreundTerm → Nat
  | .Omega => 1
  | .theta a => complexity a + 1
  | .cnf as => complexityList as + 1
def complexityList : List FreundTerm → Nat
  | [] => 0
  | a :: as => complexity a + complexityList as + 1
end
-- If a < b < Ω then a < Ω
theorem FreundTerm_lt_Omega_trans {a b : FreundTerm} (hab : a <f b) (hbO : b <f .Omega) :
        a <f .Omega := by
  cases hbO with
  | theta_Omega =>
      cases hab with
      | theta_theta_forward => exact FreundTerm_lt.theta_Omega
      | theta_theta_support_lt => exact FreundTerm_lt.theta_Omega
      | theta_theta_support_eq => exact FreundTerm_lt.theta_Omega
      | cnf_nil_theta => exact FreundTerm_lt.cnf_nil_Omega
      | cnf_theta h =>
          exact FreundTerm_lt.cnf_Omega
            (FreundTerm_lt_Omega_trans h FreundTerm_lt.theta_Omega)
  | cnf_nil_Omega =>
      cases hab with
      | cnf_cnf hlist => cases hlist
  | cnf_Omega hb =>
      cases hab with
      | Omega_cnf_lt h =>
          have hOO : (.Omega : FreundTerm) <f .Omega :=
            FreundTerm_lt_Omega_trans h hb
          cases hOO
      | Omega_cnf_eq => cases hb
      | theta_cnf_lt => exact FreundTerm_lt.theta_Omega
      | theta_cnf_eq => exact FreundTerm_lt.theta_Omega
      | cnf_cnf hlist =>
          cases hlist with
          | nil => exact FreundTerm_lt.cnf_nil_Omega
          | head h =>
              exact FreundTerm_lt.cnf_Omega
                (FreundTerm_lt_Omega_trans h hb)
          | tail => exact FreundTerm_lt.cnf_Omega hb
termination_by FreundTerm.complexity a + FreundTerm.complexity b
decreasing_by
  all_goals subst_vars
  all_goals simp [FreundTerm.complexity, FreundTerm.complexityList]
  all_goals omega
-- Mixed version
theorem FreundTerm_lt_Omega_of_le_of_lt {a b : FreundTerm} (hab : a ≤f b) (hbO : b <f .Omega) :
        a <f .Omega := by
  rcases hab with hab | hab
  · exact FreundTerm_lt_Omega_trans hab hbO
  · subst a
    exact hbO
-- Given a normal list a :: as, if a < Ω, then all components are also < Ω
theorem FreundTermList_normal_tail_lt_Omega {a : FreundTerm} {as : List FreundTerm}
        (hnormal : FreundTermList_normal (a :: as)) (haO : a <f .Omega) :
        ∀ t, t ∈ as → t <f .Omega := by
  intro t ht
  have hta : t ≤f a := FreundTermList_normal_tail_bounded hnormal t ht
  exact FreundTerm_lt_Omega_of_le_of_lt hta haO
theorem mem_treeList_iff {u : GapTree} {as : List FreundTerm} :
        u ∈ treeList as ↔ ∃ a ∈ as, tree a = u := by
  induction as with
  | nil => simp
  -- as = a :: as
  -- ih : ∀ bs < as, u ∈ treeList bs ↔ ∃ b ∈ bs, tree b = u
  | cons a as ih =>
    rw [treeList_cons]; simp only [List.mem_cons]; constructor
    · intro hu
      rcases hu with rfl | hu
      · exact ⟨a, Or.inl rfl, rfl⟩
      · obtain ⟨b, hb, hbu⟩ := ih.mp hu
        exact ⟨b, Or.inr hb, hbu⟩
    · rintro ⟨b, hb, rfl⟩
      rcases hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr (ih.mpr ⟨b, hb, rfl⟩)
-- If the head of a list is <Ω, then i (the root node) is 0
theorem treeList_rootLabel_eq_label0_of_normal_lt_Omega {a : FreundTerm} {as : List FreundTerm}
        (hnormal : FreundTermList_normal (a :: as)) (haO : a <f .Omega) :
        ∀ u, u ∈ treeList (a :: as) → GapTree.rootLabel u = GapTree.label0 := by
  intro u hu
  -- ht : t ∈ treeList (a :: as), rfl : tree t = u
  obtain ⟨t, ht, rfl⟩ := mem_treeList_iff.mp hu
  simp only [List.mem_cons] at ht
  -- rfl : r = (head of treeList (a :: as)), ht : r ∈ (tail)
  rcases ht with rfl | ht
  · exact tree_rootLabel_eq_label0_of_lt_Omega haO
  · have htO : t <f .Omega := FreundTermList_normal_tail_lt_Omega hnormal haO t ht
    exact tree_rootLabel_eq_label0_of_lt_Omega htO
-- Simply the negation as we are in the realm of N=1 (i.e., i can only be 1 or 2)
theorem treeList_no_label1_of_normal_lt_Omega {a : FreundTerm} {as : List FreundTerm}
        (hnormal : FreundTermList_normal (a :: as)) (haO : a <f .Omega) :
        ¬ ∃ u ∈ treeList (a :: as), GapTree.rootLabel u = GapTree.label1 := by
  rintro ⟨u, hu, h1⟩
  have h0 : GapTree.rootLabel u = GapTree.label0 :=
            treeList_rootLabel_eq_label0_of_normal_lt_Omega
      hnormal haO u hu
  have h01 : GapTree.label0 = GapTree.label1 := by
    exact h0.symm.trans h1
  have hval : (0 : Nat) = 1 := by
    exact congrArg Fin.val h01
  omega
end FreundTerm
/- Some clarification.
   So far, after defining the Freund term, we defined map "E" to define the "critical 0-subterms"
   of the input and map "tree" to define the corresponding "two-labeled gap tree" for encoding.
   Recall, GapTree.collapseWrap represented the tree pattern used for a collapsed ϑ-term. The
   GapTree.Ebar scanes one tree and returns the critical collapse-shaped pieces inside. So, we are
   left to show
                  Ebar [tree (a)] = tree [E(a)]
   (LHS) : After converting a FreundTerm to the tree structure we defined, we return the collapsed
           tree.
   (RHS) : After converting the input FreundTerm into the critical 0-subterm, using Freund's words,
           we retrieve the tree representation.
   This section connects are GapTree encoding with the FreundTerms-/
namespace FreundTerm
-- Ebar (ϑ (Ω)) = ∅
@[simp]
theorem Ebar_tree_Omega : GapTree.Ebar (tree .Omega) = (E .Omega).map tree := by
  simp [tree, E, GapTree.Ebar, GapTree.EbarForest, GapTree.node1]
-- for ϑ
@[simp]
theorem Ebar_tree_theta (a : FreundTerm) : GapTree.Ebar (tree (.theta a))
        = (E (.theta a)).map tree := by
  simp [E]
theorem Ebar_tree_cnf_eq_EbarForest
    {as : List FreundTerm}
    (has : FreundTermList_normal as) :
    GapTree.Ebar (tree (.cnf as)) =
      GapTree.EbarForest (treeList as) := by
  cases as with
  | nil => simp [tree, cnfLabel, GapTree.Ebar]
  | cons a as =>
      by_cases haO : a <f .Omega
      · have hno : ¬ ∃ u ∈ treeList (a :: as), GapTree.rootLabel u = GapTree.label1 :=
          treeList_no_label1_of_normal_lt_Omega has haO
        have hlabel : cnfLabel (a :: as) = GapTree.label0 := by
          simp [cnfLabel, haO]
        rw [tree, hlabel, GapTree.Ebar]
        change
          (if GapTree.label0 = GapTree.label0 ∧
                ∃ u ∈ treeList (a :: as),
                  GapTree.rootLabel u = GapTree.label1
           then [GapTree.node GapTree.label0 (treeList (a :: as))]
           else GapTree.EbarForest (treeList (a :: as))) =
            GapTree.EbarForest (treeList (a :: as))
        have hcrit :
            ¬ (GapTree.label0 = GapTree.label0 ∧
              ∃ u ∈ treeList (a :: as),
                GapTree.rootLabel u = GapTree.label1) := by
          intro h
          exact hno h.2
        rw [if_neg hcrit]
      · simp [tree, cnfLabel, haO, GapTree.Ebar, GapTree.label0, GapTree.label1]
mutual
theorem Ebar_tree_eq_map_E {a : FreundTerm} (ha : FreundTerm_normal a) :
        GapTree.Ebar (tree a) = (E a).map tree := by
  cases ha with
  | Omega => exact Ebar_tree_Omega
  | @theta a ha => exact Ebar_tree_theta a
  | @cnf as has hsingle =>
    calc GapTree.Ebar (tree (.cnf as)) = GapTree.EbarForest (treeList as) :=
      Ebar_tree_cnf_eq_EbarForest has
    _ = (EList as).map tree := EbarForest_treeList_eq_map_EList has
    _ = (E (.cnf as)).map tree := by rfl
theorem EbarForest_treeList_eq_map_EList {as : List FreundTerm} (has : FreundTermList_normal as) :
        GapTree.EbarForest (treeList as) = (EList as).map tree := by
  cases has with
  | nil => rfl
  | @single a ha => change GapTree.Ebar (tree a) ++ [] = (E a ++ []).map tree
                    rw [Ebar_tree_eq_map_E ha]
                    simp
  | @cons a b rest ha htail hbound =>
      change GapTree.Ebar (tree a) ++ GapTree.EbarForest (treeList (b :: rest))
             = (E a ++ EList (b :: rest)).map tree
      rw [Ebar_tree_eq_map_E ha]
      rw [EbarForest_treeList_eq_map_EList htail]
      simp
end
end FreundTerm

--========================================================================================
-- Gap-Tree Order

-- Some helpers to swtich between data types (List has order, multiset does not)
theorem multiset_coe_middle (before after : List GapTree) (t : GapTree) :
        (↑(before ++ (t :: after)) : Multiset GapTree) =
        t ::ₘ (↑(before ++ after) : Multiset GapTree) := by
  rw [← Multiset.coe_add before (t :: after)]
  rw [← Multiset.coe_add before after]
  rw [← Multiset.cons_coe t after]
  rw [← Multiset.singleton_add t (↑after : Multiset GapTree)]
  rw [← Multiset.singleton_add t
    ((↑before : Multiset GapTree) + (↑after : Multiset GapTree))]
  ac_rfl
theorem GapForestEmbeds_to_multiset {ss ts : List GapTree} (h : GapForestEmbeds ss ts) :
        ∃ us : Multiset GapTree, Multiset.Rel GapTreeEmbeds (↑ss : Multiset GapTree) us ∧
        us ≤ (↑ts : Multiset GapTree) := by
  cases h with
  | nil => exact ⟨0, Multiset.Rel.zero, Multiset.zero_le _⟩
  | @cons s t ss before after hst hrest =>
      obtain ⟨us, hrel, hle⟩ := GapForestEmbeds_to_multiset hrest
      refine ⟨t ::ₘ us, ?_, ?_⟩
      · simpa using Multiset.Rel.cons hst hrel
      · rw [multiset_coe_middle before after t]
        exact Multiset.cons_le_cons t hle
theorem GapForestEmbeds_of_multiset {ss ts : List GapTree}
        (h : ∃ us : Multiset GapTree, Multiset.Rel GapTreeEmbeds (↑ss : Multiset GapTree) us ∧
             us ≤ (↑ts : Multiset GapTree)) :
        GapForestEmbeds ss ts := by
  induction ss generalizing ts with
  | nil => exact GapForestEmbeds.nil
  | cons s ss ih =>
      obtain ⟨us, hrel, hle⟩ := h
      change Multiset.Rel GapTreeEmbeds (s ::ₘ (↑ss : Multiset GapTree)) us at hrel
      obtain ⟨t, us', hst, hrel', hus⟩ := Multiset.rel_cons_left.mp hrel
      rw [hus] at hle
      have htM : t ∈ (↑ts : Multiset GapTree) :=
        Multiset.mem_of_le hle (Multiset.mem_cons_self t us')
      have ht : t ∈ ts := by simpa using htM
      obtain ⟨before, after, hts⟩ := List.append_of_mem ht
      rw [hts] at hle
      rw [multiset_coe_middle before after t] at hle
      have hle' : us' ≤ (↑(before ++ after) : Multiset GapTree) :=
        (Multiset.cons_le_cons_iff t).mp hle
      have hrest : GapForestEmbeds ss (before ++ after) :=
        ih ⟨us', hrel', hle'⟩
      rw [hts]
      exact GapForestEmbeds.cons hst hrest

theorem GapForestEmbeds_extract {before after : List GapTree} {s : GapTree} {ts : List GapTree}
        (h : GapForestEmbeds (before ++ (s :: after)) ts) :
        ∃ t before' after', ts = before' ++ (t :: after') ∧ GapTreeEmbeds s t ∧
                            GapForestEmbeds (before ++ after) (before' ++ after') := by
  obtain ⟨us, hrel, hle⟩ := GapForestEmbeds_to_multiset h
  rw [multiset_coe_middle before after s] at hrel
  obtain ⟨t, us', hst, hrel', hus⟩ :=
    Multiset.rel_cons_left.mp hrel
  rw [hus] at hle
  have htM : t ∈ (↑ts : Multiset GapTree) := Multiset.mem_of_le hle (Multiset.mem_cons_self t us')
  have ht : t ∈ ts := by simpa using htM
  obtain ⟨before', after', hts⟩ := List.append_of_mem ht
  rw [hts] at hle
  rw [multiset_coe_middle before' after' t] at hle
  have hle' : us' ≤ (↑(before' ++ after') : Multiset GapTree) :=
    (Multiset.cons_le_cons_iff t).mp hle
  have hrest : GapForestEmbeds (before ++ after) (before' ++ after') :=
    GapForestEmbeds_of_multiset ⟨us', hrel', hle'⟩
  exact ⟨t, before', after', hts, hst, hrest⟩

namespace GapTree
mutual
def transComplexity : GapTree → Nat
  | .node _ ts => transComplexityList ts + 1
def transComplexityList : List GapTree → Nat
  | [] => 0
  | t :: ts => transComplexity t + transComplexityList ts
end

@[simp]
theorem transComplexityList_append (before after : List GapTree) :
    transComplexityList (before ++ after) =
      transComplexityList before + transComplexityList after := by
  induction before with
  | nil => simp [transComplexityList]
  | cons t before ih => simp [transComplexityList, ih, Nat.add_assoc]

theorem transComplexity_pos (t : GapTree) : 0 < transComplexity t := by
  cases t
  simp [transComplexity]
end GapTree

-- Embedding is transitive
mutual
theorem GapTreeEmbeds_trans {r s t : GapTree} (hrs : GapTreeEmbeds r s) (hst : GapTreeEmbeds s t) :
        GapTreeEmbeds r t := by
  cases hst with
  | @root n ss ts hstForest =>
  -- When same node and ss embeds into ts
    cases hrs with
    | root hrsForest =>
    -- rs embeds into ss
      exact GapTreeEmbeds.root (GapForestEmbeds_trans hrsForest hstForest)
    | @descend r s₀ _ before after hlabel hrsSub =>
      obtain ⟨u, before', after', hts, hs₀u, _⟩ :=
        GapForestEmbeds_extract (before := before) (after := after) (s := s₀) hstForest
      rw [hts]
      apply GapTreeEmbeds.descend hlabel
      exact GapTreeEmbeds_trans hrsSub hs₀u
  | @descend s t₀ n before after hlabel hstSub =>
    apply GapTreeEmbeds.descend
    · exact le_trans (GapTreeEmbeds_rootLabel_le hrs) hlabel
    · exact GapTreeEmbeds_trans hrs hstSub
termination_by
  GapTree.transComplexity r + GapTree.transComplexity s + GapTree.transComplexity t
decreasing_by
  all_goals subst_vars
  all_goals simp [GapTree.transComplexity, GapTree.transComplexityList]
  all_goals omega

theorem GapForestEmbeds_trans {rs ss ts : List GapTree} (hrs : GapForestEmbeds rs ss)
        (hst : GapForestEmbeds ss ts) : GapForestEmbeds rs ts := by
  cases hrs with
  | nil => exact GapForestEmbeds.nil
  | @cons r s rs before after hrsTree hrsRest =>
      obtain ⟨t, before', after', hts, hstTree, hstRest⟩ :=
        GapForestEmbeds_extract (before := before) (after := after) (s := s) hst
      rw [hts]
      exact GapForestEmbeds.cons
        (GapTreeEmbeds_trans hrsTree hstTree)
        (GapForestEmbeds_trans hrsRest hstRest)
termination_by
  GapTree.transComplexityList rs + GapTree.transComplexityList ss +
    GapTree.transComplexityList ts + 1
decreasing_by
  all_goals subst_vars
  all_goals have hr := GapTree.transComplexity_pos r
  all_goals have hs := GapTree.transComplexity_pos s
  all_goals have ht := GapTree.transComplexity_pos t
  all_goals simp [GapTree.transComplexity, GapTree.transComplexityList]
  all_goals omega
end

/- If
             1
          /  |  \
        s₀  s₁  ...
embeds into t, then each child sᵢ itself embeds into t.-/
theorem GapTreeEmbeds_children_of_node1 {ss : List GapTree} {t : GapTree}
        (h : GapTreeEmbeds (.node GapTree.label1 ss) t) :
        ∀ s, s ∈ ss → GapTreeEmbeds s t := by
  intro s hs
  -- hss : before ++ (ss :: after)
  obtain ⟨before, after, hss⟩ := List.append_of_mem hs
  have hchild : GapTreeEmbeds s (.node GapTree.label1 ss) := by
    rw [hss]; exact GapTreeEmbeds_into_parent (GapTree_le_label1 _)
  exact GapTreeEmbeds_trans hchild h

/-
If the encoding of θa embeds into the encoding of b, then it already
embeds into the encoding of some critical term γ ∈ E(b).

Uses:
    collapseWrap_embeds_Ebar
              +
    Ebar_tree_eq_map_E
-/
namespace FreundTerm
theorem theta_tree_embeds_support {a b : FreundTerm} (_ha : FreundTerm_normal a)
        (hb : FreundTerm_normal b)
        (h : GapTreeEmbeds (tree (.theta a)) (tree b)) :
        ∃ γ, γ ∈ E b ∧ GapTreeEmbeds (tree (.theta a)) (tree γ) := by
  have hwrap : GapTreeEmbeds (GapTree.collapseWrap (tree a)) (tree b) := by
    simpa using h
  obtain ⟨u, huEbar, huEmbed⟩ := collapseWrap_embeds_Ebar hwrap
  have hEbar : GapTree.Ebar (tree b) = (E b).map tree := Ebar_tree_eq_map_E hb
  rw [hEbar] at huEbar
  obtain ⟨γ, hγE, hγtree⟩ := List.mem_map.mp huEbar
  refine ⟨γ, hγE, ?_⟩
  simpa [hγtree] using huEmbed

theorem treeList_embedding_head {a : FreundTerm} {as bs : List FreundTerm}
        (h : GapForestEmbeds (treeList (a :: as)) (treeList bs)) :
        ∃ b, b ∈ bs ∧ GapTreeEmbeds (tree a) (tree b) := by
  have ha_mem : tree a ∈ (treeList (a :: as)) := by simp [treeList]
  obtain ⟨u, hu, hau⟩ := GapForestEmbeds_exists_of_mem h ha_mem
  obtain ⟨b, hb, hbu⟩ := FreundTerm.mem_treeList_iff.mp hu
  refine ⟨b, hb, ?_⟩
  rw [hbu]
  exact hau


mutual
theorem E_mem_complexity_le {a g : FreundTerm} (hg : g ∈ E a) : complexity g ≤ complexity a := by
  cases a with
  | Omega => simp [E] at hg
  | theta a => simp [E] at hg
               subst g
               exact le_rfl
  | cnf as => change g ∈ EList as at hg
              have h := EList_mem_complexity_lt hg
              simp only [complexity]
              omega
theorem EList_mem_complexity_lt {as : List FreundTerm} {g : FreundTerm} (hg : g ∈ EList as) :
        complexity g < complexityList as + 1 := by
  cases as with
  | nil => simp [EList] at hg
  | cons a as => change g ∈ E a ++ EList as at hg
                 simp only [List.mem_append] at hg
                 rcases hg with hga | hgas
                 · have hle : complexity g ≤ complexity a :=
                    E_mem_complexity_le hga
                   simp only [complexityList]
                   omega
                 · have hlt : complexity g < complexityList as + 1 :=
                    EList_mem_complexity_lt hgas
                   simp only [complexityList]
                   omega
end
theorem E_mem_complexity_lt_theta {a g : FreundTerm} (hg : g ∈ E a) :
        complexity g < complexity (.theta a) := by
  have h := E_mem_complexity_le hg
  simp only [complexity]
  omega

mutual
theorem FreundTerm_lt_trans {a b c : FreundTerm} (hab : a <f b) (hbc : b <f c) : a <f c := by
  have habCopy := hab; have hbcCopy := hbc
  cases hbc with
  | Omega_cnf_lt cHead => cases hab with
                          | theta_Omega =>
                            exact FreundTerm_lt.theta_cnf_lt
                                  (FreundTerm_lt_trans FreundTerm_lt.theta_Omega cHead)
                          | cnf_nil_Omega => exact FreundTerm_lt.cnf_cnf FreundTermList_lt.nil
                          | cnf_Omega aHead =>
                            exact FreundTerm_lt.cnf_cnf
                                  (FreundTermList_lt.head (FreundTerm_lt_trans aHead cHead))
  | Omega_cnf_eq => cases hab with
                    | theta_Omega => exact FreundTerm_lt.theta_cnf_lt FreundTerm_lt.theta_Omega
                    | cnf_nil_Omega => exact FreundTerm_lt.cnf_cnf FreundTermList_lt.nil
                    | cnf_Omega aHead => exact FreundTerm_lt.cnf_cnf (FreundTermList_lt.head aHead)
  | theta_Omega => cases hab with
                   | theta_theta_forward => exact FreundTerm_lt.theta_Omega
                   | theta_theta_support_lt => exact FreundTerm_lt.theta_Omega
                   | theta_theta_support_eq => exact FreundTerm_lt.theta_Omega
                   | cnf_nil_theta => exact FreundTerm_lt.cnf_nil_Omega
                   | cnf_theta h =>
                     exact FreundTerm_lt.cnf_Omega
                           (FreundTerm_lt_Omega_trans h FreundTerm_lt.theta_Omega)

  | theta_cnf_lt hbcHead => cases hab with
                            | theta_theta_forward =>
                              exact FreundTerm_lt.theta_cnf_lt (FreundTerm_lt_trans habCopy hbcHead)
                            | theta_theta_support_lt =>
                              exact FreundTerm_lt.theta_cnf_lt (FreundTerm_lt_trans habCopy hbcHead)
                            | theta_theta_support_eq =>
                              exact FreundTerm_lt.theta_cnf_lt (FreundTerm_lt_trans habCopy hbcHead)
                            | cnf_nil_theta =>
                              exact FreundTerm_lt.cnf_cnf FreundTermList_lt.nil
                            | cnf_theta habHead =>
                              exact FreundTerm_lt.cnf_cnf (FreundTermList_lt.head
                                      (FreundTerm_lt_trans habHead hbcHead))
  | theta_cnf_eq => cases hab with
                    | theta_theta_forward => exact FreundTerm_lt.theta_cnf_lt habCopy
                    | theta_theta_support_lt => exact FreundTerm_lt.theta_cnf_lt habCopy
                    | theta_theta_support_eq => exact FreundTerm_lt.theta_cnf_lt habCopy
                    | cnf_nil_theta => exact FreundTerm_lt.cnf_cnf FreundTermList_lt.nil
                    | cnf_theta habHead =>
                      exact FreundTerm_lt.cnf_cnf (FreundTermList_lt.head habHead)
  | theta_theta_forward hbcArg hEbc =>
      cases hab with
      | theta_theta_forward habArg hEab =>
          apply FreundTerm_lt.theta_theta_forward
          · exact FreundTerm_lt_trans habArg hbcArg
          · intro g hg
            have hgComplexity : complexity g ≤ complexity _ := E_mem_complexity_le hg
            exact FreundTerm_lt_trans (hEab g hg) hbcCopy
      | @theta_theta_support_lt _ _ g hg hθag =>
          have hgComplexity : complexity g ≤ complexity _ := E_mem_complexity_le hg
          exact FreundTerm_lt_trans hθag (hEbc g hg)
      | theta_theta_support_eq hg => exact hEbc _ hg
      | cnf_nil_theta => exact FreundTerm_lt.cnf_nil_theta
      | cnf_theta hHead => exact FreundTerm_lt.cnf_theta (FreundTerm_lt_trans hHead hbcCopy)
  | theta_theta_support_lt hg hθbg =>
      have hgComplexity : complexity _ ≤ complexity _ :=
        E_mem_complexity_le hg
      cases hab with
      | theta_theta_forward =>
          exact FreundTerm_lt.theta_theta_support_lt hg
            (FreundTerm_lt_trans habCopy hθbg)
      | theta_theta_support_lt =>
          exact FreundTerm_lt.theta_theta_support_lt hg
            (FreundTerm_lt_trans habCopy hθbg)
      | theta_theta_support_eq =>
          exact FreundTerm_lt.theta_theta_support_lt hg
            (FreundTerm_lt_trans habCopy hθbg)
      | cnf_nil_theta =>
          exact FreundTerm_lt.cnf_nil_theta
      | cnf_theta hHead =>
          exact FreundTerm_lt.cnf_theta
            (FreundTerm_lt_trans hHead hbcCopy)
  | theta_theta_support_eq hg =>
      cases hab with
      | theta_theta_forward =>
          exact FreundTerm_lt.theta_theta_support_lt hg habCopy
      | theta_theta_support_lt =>
          exact FreundTerm_lt.theta_theta_support_lt hg habCopy
      | theta_theta_support_eq =>
          exact FreundTerm_lt.theta_theta_support_lt hg habCopy
      | cnf_nil_theta =>
          exact FreundTerm_lt.cnf_nil_theta
      | cnf_theta hHead =>
          exact FreundTerm_lt.cnf_theta
            (FreundTerm_lt_trans hHead hbcCopy)
  | cnf_nil_Omega =>
      cases hab with
      | cnf_cnf h => cases h
  | cnf_nil_theta =>
      cases hab with
      | cnf_cnf h => cases h
  | cnf_Omega hbO =>
      cases hab with
      | Omega_cnf_lt hOb =>
          have hbad : (.Omega : FreundTerm) <f .Omega :=
            FreundTerm_lt_Omega_trans hOb hbO
          cases hbad
      | Omega_cnf_eq => cases hbO
      | theta_cnf_lt => exact FreundTerm_lt.theta_Omega
      | theta_cnf_eq => exact FreundTerm_lt.theta_Omega
      | cnf_cnf habList =>
          cases habList with
          | nil => exact FreundTerm_lt.cnf_nil_Omega
          | head hHead =>
              exact FreundTerm_lt.cnf_Omega
                (FreundTerm_lt_Omega_trans hHead hbO)
          | tail => exact FreundTerm_lt.cnf_Omega hbO
  | cnf_theta hbcHead =>
      cases hab with
      | Omega_cnf_lt hOb => have hbad : (.Omega : FreundTerm) <f _ :=
                              FreundTerm_lt_trans hOb hbcHead
                            cases hbad
      | Omega_cnf_eq => cases hbcHead
      | theta_cnf_lt habHead =>
          exact FreundTerm_lt_trans habHead hbcHead
      | theta_cnf_eq => exact hbcHead
      | cnf_cnf habList =>
          cases habList with
          | nil => exact FreundTerm_lt.cnf_nil_theta
          | head hHead =>
              exact FreundTerm_lt.cnf_theta
                (FreundTerm_lt_trans hHead hbcHead)
          | tail => exact FreundTerm_lt.cnf_theta hbcHead
  | cnf_cnf hbcList =>
      cases hbcList with
      | nil =>
          cases hab with
          | cnf_cnf habList => cases habList
      | head hbcHead =>
          cases hab with
          | Omega_cnf_lt habHead =>
              exact FreundTerm_lt.Omega_cnf_lt
                (FreundTerm_lt_trans habHead hbcHead)
          | Omega_cnf_eq =>
              exact FreundTerm_lt.Omega_cnf_lt hbcHead
          | theta_cnf_lt habHead =>
              exact FreundTerm_lt.theta_cnf_lt
                (FreundTerm_lt_trans habHead hbcHead)
          | theta_cnf_eq =>
              exact FreundTerm_lt.theta_cnf_lt hbcHead
          | cnf_cnf habList =>
              exact FreundTerm_lt.cnf_cnf
                (FreundTermList_lt_trans
                  habList
                  (FreundTermList_lt.head hbcHead))
      | tail hbcTail =>
          cases hab with
          | Omega_cnf_lt habHead =>
              exact FreundTerm_lt.Omega_cnf_lt habHead
          | Omega_cnf_eq =>
              exact FreundTerm_lt.Omega_cnf_eq
          | theta_cnf_lt habHead =>
              exact FreundTerm_lt.theta_cnf_lt habHead
          | theta_cnf_eq =>
              exact FreundTerm_lt.theta_cnf_eq
          | cnf_cnf habList =>
              exact FreundTerm_lt.cnf_cnf
                (FreundTermList_lt_trans
                  habList
                  (FreundTermList_lt.tail hbcTail))
termination_by
  complexity a + complexity b + complexity c
decreasing_by
  all_goals subst_vars
  all_goals
    simp [FreundTerm.complexity,
          FreundTerm.complexityList]
  all_goals omega

theorem FreundTermList_lt_trans {as bs cs : List FreundTerm} (hab : FreundTermList_lt as bs)
    (hbc : FreundTermList_lt bs cs) : FreundTermList_lt as cs := by
  cases hab with
  | nil =>
      cases hbc with
      | head => exact FreundTermList_lt.nil
      | tail => exact FreundTermList_lt.nil
  | head habHead =>
      cases hbc with
      | head hbcHead =>
          exact FreundTermList_lt.head
            (FreundTerm_lt_trans habHead hbcHead)
      | tail => exact FreundTermList_lt.head habHead
  | tail habTail =>
      cases hbc with
      | head hbcHead => exact FreundTermList_lt.head hbcHead
      | tail hbcTail =>
          exact FreundTermList_lt.tail
            (FreundTermList_lt_trans habTail hbcTail)
  termination_by
  complexityList as +
  complexityList bs +
  complexityList cs + 1
  decreasing_by
  all_goals subst_vars
  all_goals
    simp [FreundTerm.complexity,
          FreundTerm.complexityList]
  all_goals omega
end
theorem FreundTerm_le_trans {a b c : FreundTerm} (hab : a ≤f b) (hbc : b ≤f c) :
        a ≤f c := by
  rcases hab with hab | hab
  · rcases hbc with hbc | hbc
    · exact Or.inl (FreundTerm_lt_trans hab hbc)
    · subst c; exact Or.inl hab
  · subst b; exact hbc
theorem FreundTerm_lt_of_lt_of_le {a b c : FreundTerm} (hab : a <f b) (hbc : b ≤f c) :
        a <f c := by
  rcases hbc with hbc | hbc
  · exact FreundTerm_lt_trans hab hbc
  · subst c; exact hab
theorem FreundTerm_lt_of_le_of_lt {a b c : FreundTerm} (hab : a ≤f b) (hbc : b <f c) :
        a <f c := by
  rcases hab with hab | hab
  · exact FreundTerm_lt_trans hab hbc
  · subst b; exact hbc


theorem GapForestEmbeds_cancel_head {s : GapTree} {ss ts : List GapTree}
        (h : GapForestEmbeds (s :: ss) (s :: ts)) :
        GapForestEmbeds ss ts := by
  -- ∃t before after, htarget (s :: ts = before ++ t :: after)
  -- hst : GapTreeEmbeds s t, hrest : GapForestEmbeds ss (before ++ after)
  obtain ⟨t, before, after, htarget, hst, hrest⟩ := GapForestEmbeds_head h
  cases before with
  | nil =>
    simp only [List.nil_append] at htarget hrest
    -- htarget : s :: ts = t :: after
    -- hrest : GapForestEmbeds ss [after]
    injection htarget with hst_eq htail_eq
    -- s = t / ts = after
    subst t; subst after
    -- GapForestEmbeds ss [ts]
    exact hrest
  | cons x before =>
    simp only [List.cons_append] at htarget hrest
    -- htarget : s :: ts = x :: before ++ t :: after
    -- hrest : GapForestEmbeds ss (x :: before ++ after)
    injection htarget with hx hts
    -- s = x / ts = before ++ t :: after
    subst x
    have hrest' : GapForestEmbeds ss (s :: (before ++ after)) := by
      simpa using hrest
    have hswap : GapForestEmbeds (s :: (before ++ after)) (before ++ (t :: after)) := by
      exact GapForestEmbeds.cons hst (GapForestEmbeds_refl (before ++ after))
    have hfinal : GapForestEmbeds ss (before ++ (t :: after)) :=
      GapForestEmbeds_trans hrest' hswap
    rw [hts]
    exact hfinal
-- If a FreundTermList is normal, every element of it is normal
theorem FreundTermList_normal_mem {as : List FreundTerm} (h : FreundTermList_normal as) :
        ∀ a, a ∈ as → FreundTerm_normal a := by
  intro a ha
  cases as with
  | nil => simp at ha
  | cons b bs =>
    cases bs with
    -- as = b :: []
    | nil => cases h with
             | single hb =>
               simp only [List.mem_singleton] at ha
               subst a; exact hb
    -- as = b :: (c :: crest)
    | cons c crest =>
      -- h : FreundTermList_normal (b :: c :: crest)
      cases h with
      -- hb : FreundTerm_normal b / htail : List_normal (c :: crest)
      -- hbound : ∀ t ∈ c :: crest, r ≤f b
      | cons hb htail hbound =>
        rw [List.mem_cons] at ha
        -- rfl : a = b, ha = a ∈ (c :: crest)
        rcases ha with rfl | other
        · exact hb
        · exact FreundTermList_normal_mem htail a other
def FreundTermList_le (as bs : List FreundTerm) : Prop := FreundTermList_lt as bs ∨ as = bs
infix:50 " ≤fl " => FreundTermList_le
-- E mapping (simply collapsing the theta) of normal element gives normal
mutual
theorem E_mem_normal {a g : FreundTerm} (ha : FreundTerm_normal a) (hg : g ∈ E a) :
        FreundTerm_normal g := by
  cases a with
  | Omega => simp [E] at hg
  | theta b => have hgb : g = .theta b := by
                simpa [E] using hg
               subst g
               exact ha
  | cnf as => change g ∈ EList as at hg
              cases ha with
              | cnf has hsingle => exact EList_mem_normal has hg
theorem EList_mem_normal {as : List FreundTerm} {g : FreundTerm} (has : FreundTermList_normal as)
        (hg : g ∈ EList as) : FreundTerm_normal g := by
  cases as with
  | nil => simp [EList] at hg
  | cons a as' =>
    change g ∈ E a ++ EList as' at hg
    rw [List.mem_append] at hg -- g ∈ E a ∨ g ∈ EList as
    rcases hg with hga | hgas
    · have ha : FreundTerm_normal a := FreundTermList_normal_head has
      exact E_mem_normal ha hga
    · have hasTail : FreundTermList_normal as' := FreundTermList_normal_tail has
      exact EList_mem_normal hasTail hgas
end
theorem complexity_lt_cnf_of_mem {a : FreundTerm} {as : List FreundTerm} (ha : a ∈ as) :
        complexity a < complexity (.cnf as) := by
  simp only [complexity]
  induction as with
  | nil => simp at ha
  | cons b bs ih => rw [List.mem_cons] at ha
                    rcases ha with rfl | ha'
                    · simp only [complexityList]
                      omega
                    · have hlt := ih ha'
                      simp only [complexityList]
                      omega
@[simp]
theorem complexity_lt_theta (a : FreundTerm) : complexity a < complexity (.theta a) := by
  simp [complexity]
theorem Omega_le_of_not_lt_Omega {a : FreundTerm} (h : ¬ a <f .Omega) :
        (.Omega : FreundTerm) ≤f a := by
  cases a with
  | Omega => exact Or.inr rfl
  | theta a => exfalso; exact h FreundTerm_lt.theta_Omega
  | cnf as => cases as with
              | nil => exfalso; exact h FreundTerm_lt.cnf_nil_Omega
              | cons b bs =>
                by_cases hb : b <f .Omega
                · exfalso; exact h (FreundTerm_lt.cnf_Omega hb)
                · have hOb : (.Omega : FreundTerm) ≤f b :=
                    Omega_le_of_not_lt_Omega hb
                  rcases hOb with hOb | hOb
                  · exact Or.inl (FreundTerm_lt.Omega_cnf_lt hOb)
                  · subst b; exact Or.inl FreundTerm_lt.Omega_cnf_eq
mutual

theorem GapTreeEmbeds_transComplexity_le {s t : GapTree} (h : GapTreeEmbeds s t) :
        GapTree.transComplexity s ≤ GapTree.transComplexity t := by
  cases h with
  | @root n ss ts hforest =>
      have hle := GapForestEmbeds_transComplexityList_le hforest
      simp only [GapTree.transComplexity]; omega
  | @descend s t n before after hlabel hsub =>
      have hle := GapTreeEmbeds_transComplexity_le hsub
      have htpos := GapTree.transComplexity_pos t
      simp [GapTree.transComplexity, GapTree.transComplexityList,
            GapTree.transComplexityList_append]; omega
  termination_by GapTree.transComplexity s + GapTree.transComplexity t
  decreasing_by
    all_goals subst_vars
    all_goals
      simp [
      GapTree.transComplexity,
      GapTree.transComplexityList,
      GapTree.transComplexityList_append
      ]
    all_goals omega
theorem GapForestEmbeds_transComplexityList_le {ss ts : List GapTree} (h : GapForestEmbeds ss ts) :
        GapTree.transComplexityList ss ≤ GapTree.transComplexityList ts := by
  cases h with
  | nil => simp [GapTree.transComplexityList]
  | @cons s t ss before after hst hrest =>
      have hTree := GapTreeEmbeds_transComplexity_le hst
      have hForest := GapForestEmbeds_transComplexityList_le hrest
      simp [
        GapTree.transComplexityList,
        GapTree.transComplexityList_append
      ] at *
      omega
  termination_by GapTree.transComplexityList ss +
    GapTree.transComplexityList ts + 1
  decreasing_by
    all_goals subst_vars
    all_goals have hspos := GapTree.transComplexity_pos s
    all_goals
      simp [
        GapTree.transComplexity,
        GapTree.transComplexityList,
        GapTree.transComplexityList_append
      ]
    all_goals omega
end
-- g ∈ E(a) → Ebar (g) ≤ Ebar (a)
theorem E_mem_tree_embeds {a g : FreundTerm} (ha : FreundTerm_normal a) (hg : g ∈ E a) :
        GapTreeEmbeds (tree g) (tree a) := by
  have hmem : tree g ∈ GapTree.Ebar (tree a) := by
    rw [Ebar_tree_eq_map_E ha]
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  exact Ebar_mem_embeds hmem
theorem GapTreeEmbeds_to_node_cases {s : GapTree} {n : GapLabel} {ts : List GapTree}
        (h : GapTreeEmbeds s (.node n ts)) :
        (∃ ss, s = .node n ss ∧ GapForestEmbeds ss ts) ∨
        (∃ t, t ∈ ts ∧ GapTreeEmbeds s t) := by
  cases h with
  | @root n ss ts hforest =>
    exact Or.inl ⟨ss, rfl, hforest⟩
  | @descend s t n before after hlabel hsub =>
    exact Or.inr ⟨t, by simp, hsub⟩
theorem GapTreeEmbeds_node1_singleton_cancel {s t : GapTree}
        (h : GapTreeEmbeds (.node GapTree.label1 [s]) (.node GapTree.label1 [t])) :
        GapTreeEmbeds s t := by
  rcases GapTreeEmbeds_to_node_cases h with hroot | hdesc
  -- hsource : s = .node n ss
  -- hforest : GapForestEmbeds ss ts
  · obtain ⟨ss, hsource, hforest⟩ := hroot
    have hchildren := congrArg GapTree.children hsource
    have hss : ss = [s] := by simpa using hchildren.symm
    subst ss
    have hs : s ∈ [s] := by simp
    obtain ⟨u, hu, hsu⟩ := GapForestEmbeds_exists_of_mem hforest hs
    have hu' : u = t := by simpa using hu
    subst u; exact hsu
  -- hu : t ∈ ts / hsub : GapTreeEmbeds s t
  · obtain ⟨u, hu, hsub⟩ := hdesc
    have hu' : u = t := by simpa using hu
    subst u
    exact GapTreeEmbeds_children_of_node1 hsub s (by simp)
theorem E_mem_tree_rootLabel_eq_label0 {a g : FreundTerm} (ha : FreundTerm_normal a)
        (hg : g ∈ E a) : GapTree.rootLabel (tree g) = GapTree.label0 := by
  have hmem : tree g ∈ GapTree.Ebar (tree a) := by
    rw [Ebar_tree_eq_map_E ha]; exact List.mem_map.mpr ⟨g, hg, rfl⟩
  exact Ebar_mem_rootLabel_eq_label0 hmem
-- A 0-root tree that embeds into t also embeds into the collapsed t
theorem GapTreeEmbeds_into_collapseWrap_of_root0 {s t : GapTree}
        (hroot : GapTree.rootLabel s = GapTree.label0) (h : GapTreeEmbeds s t) :
        GapTreeEmbeds s (GapTree.collapseWrap t) := by
  have h1 : GapTreeEmbeds s (.node GapTree.label1 [t]) := by
    change GapTreeEmbeds s (.node GapTree.label1 ([] ++ (t :: [])))
    exact GapTreeEmbeds.descend (GapTree_le_label1 _) h
  have h0 : GapTreeEmbeds s (.node GapTree.label0 [(.node GapTree.label1 [t])]) := by
    change GapTreeEmbeds s (.node GapTree.label0 ([] ++ ((.node GapTree.label1 [t]) :: [] )))
    apply GapTreeEmbeds.descend
    · simpa [hroot] using (le_rfl : GapTree.label0 ≤ GapTree.label0)
    · exact h1
  simpa [GapTree.collapseWrap, GapTree.node0, GapTree.node1] using h0

-- Every term is strictly below the CNF whose first entry is that term
theorem FreundTerm_lt_cnf_cons_self (a : FreundTerm) (as : List FreundTerm) :
        a <f .cnf (a :: as) := by
  cases a with
  | Omega => exact FreundTerm_lt.Omega_cnf_eq
  | theta a => exact FreundTerm_lt.theta_cnf_eq
  | cnf cs => cases cs with
              | nil => exact FreundTerm_lt.cnf_cnf FreundTermList_lt.nil
              | cons c cxs =>
                exact FreundTerm_lt.cnf_cnf (FreundTermList_lt.head
                      (FreundTerm_lt_cnf_cons_self c cxs))

theorem EList_mem_exists {as : List FreundTerm} {g : FreundTerm} (hg : g ∈ EList as) :
        ∃ a, a ∈ as ∧ g ∈ E a := by
  induction as with
  | nil => simp [EList] at hg
  | cons a as ih =>
    change g ∈ E a ++ EList as at hg
    rw [List.mem_append] at hg -- g = (EList as head), g ∈ (Elist as tail)
    rcases hg with hga | hgas
    · exact ⟨a, by simp, hga⟩
    · obtain ⟨b, hb, hgb⟩ := ih hgas
      exact ⟨b, by simp [hb], hgb⟩
theorem E_mem_le_self {a g : FreundTerm} (ha : FreundTerm_normal a) (hg : g ∈ E a) : g ≤f a := by
  cases a with
  | Omega => simp [E] at hg
  | theta a => have hg' : g = .theta a := by
                simpa [E] using hg
               subst g; exact Or.inr rfl
  | cnf as =>
    cases ha with
    /- cnf {as : List FreundTerm} (has : FreundTermList_normal as)
        (hsingle : ∀ a, as = [a] → FreundSingletonOK a) -/
    | cnf has hsingle =>
      change g ∈ EList as at hg
      -- c : ∃ c, hc : c ∈ as, hgc : g ∈ a.E
      obtain ⟨c, hc, hgc⟩ := EList_mem_exists hg
      have hcNormal : FreundTerm_normal c := FreundTermList_normal_mem has c hc
      have hcCmplx : complexity c < complexity (.cnf as) := complexity_lt_cnf_of_mem hc
      have hgcLe : g ≤f c := E_mem_le_self hcNormal hgc
      cases as with
      | nil => simp at hc
      | cons ax axs => have hcHead : c ≤f ax := by
                        simp only [List.mem_cons] at hc
                        rcases hc with rfl | hc
                        · exact Or.inr rfl
                        · exact FreundTermList_normal_tail_bounded has c hc
                       have hgHead : g ≤f ax :=
                        FreundTerm_le_trans hgcLe hcHead
                       exact Or.inl (FreundTerm_lt_of_le_of_lt hgHead
                             (FreundTerm_lt_cnf_cons_self ax axs))
-- Critical terms of a CNF term are strictly below the whole CNF term
theorem E_mem_lt_cnf {as : List FreundTerm} {g : FreundTerm} (ha : FreundTerm_normal (.cnf as))
        (hg : g ∈ E (.cnf as)) : g <f .cnf as := by
  have hle : g ≤f .cnf as := E_mem_le_self ha hg
  rcases hle with hlt | heq
  · exact hlt
  · have hg' := hg; change g ∈ EList as at hg'
    have hcmplx := EList_mem_complexity_lt hg'
    subst g
    simp only [complexity] at hcmplx; omega

-- Root label bound
theorem tree_mem_rootLabel_le_cnfLabel {a : FreundTerm} {as : List FreundTerm}
        (has : FreundTermList_normal as) (ha : a ∈ as) :
        GapTree.rootLabel (tree a) ≤ cnfLabel as := by
  cases as with
  | nil => simp at ha
  | cons b bs =>
    by_cases hb : b <f .Omega
    · have haO : a <f .Omega := by
       simp only [List.mem_cons] at ha
       rcases ha with rfl | ha
       · exact hb
       · exact FreundTermList_normal_tail_lt_Omega has hb a ha
      have hroot : GapTree.rootLabel (tree a) = GapTree.label0 :=
        tree_rootLabel_eq_label0_of_lt_Omega haO
      have hlabel : cnfLabel (b :: bs) = GapTree.label0 := by
        simp [cnfLabel, hb]
      rw [hroot, hlabel]
    · have hlabel : cnfLabel (b :: bs) = GapTree.label1 :=
        cnfLabel_cons_of_lt hb
      rw [hlabel]; exact GapTree_le_label1 _

theorem tree_mem_embeds_cnf {a : FreundTerm} {as : List FreundTerm} (has : FreundTermList_normal as)
        (ha : a ∈ as) : GapTreeEmbeds (tree a) (tree (.cnf as)) := by
  have hmem : tree a ∈ treeList as := by exact mem_treeList_iff.mpr ⟨a, ha, rfl⟩
  obtain ⟨before, after, hlist⟩ := List.append_of_mem hmem
  change GapTreeEmbeds (tree a) (.node (cnfLabel as) (treeList as))
  rw [hlist]
  exact GapTreeEmbeds_into_parent (tree_mem_rootLabel_le_cnfLabel has ha)
-- The head tree is a proper subtree, in the node-count sense, of its CNF tree
theorem tree_head_transComplexity_lt_cnf (a : FreundTerm) (as : List FreundTerm) :
        GapTree.transComplexity (tree a) < GapTree.transComplexity (tree (.cnf (a :: as))) := by
  simp [tree, treeList, GapTree.transComplexity, GapTree.transComplexityList]
-- Adding a theta-wrapper strictly increases tree complexity
theorem tree_transComplexity_lt_theta (a : FreundTerm) :
        GapTree.transComplexity (tree a) < GapTree.transComplexity (tree (.theta a)) := by
  simp [tree, GapTree.collapseWrap, GapTree.node0, GapTree.node1, GapTree.transComplexity,
        GapTree.transComplexityList]

mutual

theorem tree_embedding_le {a b : FreundTerm} (ha : FreundTerm_normal a) (hb : FreundTerm_normal b)
        (h : GapTreeEmbeds (tree a) (tree b)) : a ≤f b := by
  cases a with
  | Omega =>
    cases b with
    | Omega => exact Or.inr rfl
    | theta b =>
        exfalso
        have hroot := GapTreeEmbeds_rootLabel_le h
        have hbad : GapTree.label1 ≤ GapTree.label0 := by
          simpa [tree] using hroot
        change (1 : Nat) ≤ 0 at hbad
        omega
    | cnf bs =>
        cases hb with
        | cnf hbs hsingle =>
          have hnode : GapTreeEmbeds (tree (.Omega : FreundTerm))
                       (.node (cnfLabel bs) (treeList bs)) := by
            simpa [tree] using h
          rcases GapTreeEmbeds_to_node_cases hnode with hroot | hdesc
          · obtain ⟨ss, hsource, hforest⟩ := hroot
            have hrootEq := congrArg GapTree.rootLabel hsource
            have hlabel : GapTree.label1 = cnfLabel bs := by
              simpa [tree] using hrootEq
            cases bs with
            | nil =>
                have hbad : GapTree.label1 = GapTree.label0 := by
                  simpa [cnfLabel] using hlabel
                have hv := congrArg Fin.val hbad
                simp [GapTree.label0, GapTree.label1] at hv
            | cons b bs =>
                have hbNot : ¬ b <f .Omega := by
                  intro hbO
                  have h0 : cnfLabel (b :: bs) = GapTree.label0 := by
                    simp [cnfLabel, hbO]
                  have hbad : GapTree.label1 = GapTree.label0 :=
                    hlabel.trans h0
                  have hv := congrArg Fin.val hbad
                  simp [GapTree.label0, GapTree.label1] at hv
                have hOb : (.Omega : FreundTerm) ≤f b :=
                  Omega_le_of_not_lt_Omega hbNot
                exact Or.inl
                  (FreundTerm_lt_of_le_of_lt
                    hOb
                    (FreundTerm_lt_cnf_cons_self b bs))
          · obtain ⟨u, hu, hOu⟩ := hdesc
            obtain ⟨c, hc, hcu⟩ := mem_treeList_iff.mp hu
            subst u
            have hcNormal : FreundTerm_normal c :=
              FreundTermList_normal_mem hbs c hc
            have hcCmplx : complexity c < complexity (.cnf bs) :=
              complexity_lt_cnf_of_mem hc
            have hOc : (.Omega : FreundTerm) ≤f c :=
              tree_embedding_le
                FreundTerm_normal.Omega
                hcNormal
                hOu
            cases bs with
            | nil => simp at hc
            | cons b bs =>
                have hcb : c ≤f b := by
                  simp only [List.mem_cons] at hc
                  rcases hc with rfl | hc
                  · exact Or.inr rfl
                  · exact
                      FreundTermList_normal_tail_bounded hbs c hc
                have hOb : (.Omega : FreundTerm) ≤f b :=
                  FreundTerm_le_trans hOc hcb
                exact Or.inl
                  (FreundTerm_lt_of_le_of_lt
                    hOb
                    (FreundTerm_lt_cnf_cons_self b bs))
  | theta a =>
    cases ha with
    | theta ha =>
      cases b with
      | Omega =>
          exact Or.inl FreundTerm_lt.theta_Omega
      | theta b =>
          cases hb with
          | theta hb =>
            have hnode : GapTreeEmbeds (GapTree.collapseWrap (tree a))
                         (.node GapTree.label0 [GapTree.node1 [tree b]]) := by
              simpa [tree, GapTree.collapseWrap, GapTree.node0] using h
            rcases GapTreeEmbeds_to_node_cases hnode with hroot | hdesc
            · obtain ⟨ss, hsource, hforest⟩ := hroot
              have hchildren := congrArg GapTree.children hsource
              have hss : ss = [GapTree.node1 [tree a]] := by
                simpa [ GapTree.collapseWrap, GapTree.node0] using hchildren.symm
              subst ss
              obtain ⟨u, hu, hinner⟩ :=
                GapForestEmbeds_exists_of_mem
                  (s := GapTree.node1 [tree a])
                  hforest
                  (by simp)
              have hu' : u = GapTree.node1 [tree b] := by
                simpa using hu
              subst u
              have harg : GapTreeEmbeds (tree a) (tree b) := by
                apply GapTreeEmbeds_node1_singleton_cancel
                simpa [GapTree.node1] using hinner
              have hab : a ≤f b := tree_embedding_le ha hb harg
              rcases hab with hab | hab
              · apply Or.inl
                apply FreundTerm_lt.theta_theta_forward hab
                intro g hg
                have hgNormal : FreundTerm_normal g := E_mem_normal ha hg
                have hgCmplx : complexity g ≤ complexity a :=
                  E_mem_complexity_le hg
                have hgA : GapTreeEmbeds (tree g) (tree a) :=
                  E_mem_tree_embeds ha hg
                have hgB : GapTreeEmbeds (tree g) (tree b) :=
                  GapTreeEmbeds_trans hgA harg
                have hgRoot : GapTree.rootLabel (tree g) = GapTree.label0 :=
                  E_mem_tree_rootLabel_eq_label0 ha hg
                have hgThetaB : GapTreeEmbeds (tree g) (tree (.theta b)) := by
                  simpa [tree] using
                    GapTreeEmbeds_into_collapseWrap_of_root0
                      hgRoot hgB
                have hgLe : g ≤f .theta b :=
                  tree_embedding_le hgNormal (FreundTerm_normal.theta hb) hgThetaB
                rcases hgLe with hgLt | hgEq
                · exact hgLt
                · subst g
                  have hsize := GapTreeEmbeds_transComplexity_le hgB
                  have hstrict := tree_transComplexity_lt_theta b
                  omega
              · subst b
                exact Or.inr rfl
            · obtain ⟨u, hu, hsub⟩ := hdesc
              have hu' : u = GapTree.node1 [tree b] := by
                simpa using hu
              subst u
              have hnode1 :
                  GapTreeEmbeds
                    (GapTree.collapseWrap (tree a))
                    (.node GapTree.label1 [tree b]) := by
                simpa [GapTree.node1] using hsub
              rcases GapTreeEmbeds_to_node_cases hnode1 with hroot1 | hdesc1
              · obtain ⟨ss, hbad, hforest⟩ := hroot1
                have hv := congrArg (fun t => (GapTree.rootLabel t).val) hbad
                simp [GapTree.collapseWrap, GapTree.node0, GapTree.node1,
                      GapTree.label0, GapTree.label1] at hv
              · obtain ⟨v, hv, hintoB⟩ := hdesc1
                have hv' : v = tree b := by simpa using hv
                subst v
                have hthetaB : GapTreeEmbeds (tree (.theta a)) (tree b) := by
                  simpa [tree] using hintoB
                obtain ⟨γ, hγE, hθγ⟩ := theta_tree_embeds_support ha hb hthetaB
                have hγNormal : FreundTerm_normal γ := E_mem_normal hb hγE
                have hγCmplx : complexity γ ≤ complexity b := E_mem_complexity_le hγE
                have hle : (.theta a : FreundTerm) ≤f γ :=
                  tree_embedding_le
                    (FreundTerm_normal.theta ha)
                    hγNormal
                    hθγ
                rcases hle with hlt | heq
                · exact Or.inl
                    (FreundTerm_lt.theta_theta_support_lt
                      hγE hlt)
                · subst γ
                  exact Or.inl
                    (FreundTerm_lt.theta_theta_support_eq
                      hγE)
      | cnf bs =>
          cases hb with
          | cnf hbs hsingle =>
            obtain ⟨γ, hγE, hθγ⟩ :=
              theta_tree_embeds_support
                ha
                (FreundTerm_normal.cnf hbs hsingle)
                h
            have hγNormal : FreundTerm_normal γ :=
              E_mem_normal (FreundTerm_normal.cnf hbs hsingle) hγE
            have hγE' := hγE
            change γ ∈ EList bs at hγE'
            have hγCmplx0 := EList_mem_complexity_lt hγE'
            have hγCmplx : complexity γ < complexity (.cnf bs) := by
              simpa [complexity] using hγCmplx0
            have hθγLe : (.theta a : FreundTerm) ≤f γ :=
              tree_embedding_le (FreundTerm_normal.theta ha) hγNormal hθγ
            have hγTarget : γ <f .cnf bs :=
              E_mem_lt_cnf (FreundTerm_normal.cnf hbs hsingle) hγE
            exact Or.inl (FreundTerm_lt_of_le_of_lt hθγLe hγTarget)
  | cnf as =>
    cases ha with
    | cnf has hsingle =>
      cases b with
      | Omega =>
          have hnode : GapTreeEmbeds (tree (.cnf as)) (.node GapTree.label1 []) := by
            simpa [tree, GapTree.node1] using h
          rcases GapTreeEmbeds_to_node_cases hnode with hroot | hdesc
          · obtain ⟨ss, hsource, hembed⟩ := hroot
            have hss : ss = [] := by
              cases ss with
              | nil => rfl
              | cons s ss =>
                  have hsMem : s ∈ s :: ss := by simp
                  obtain ⟨u, hu, _⟩ :=
                    GapForestEmbeds_exists_of_mem hembed hsMem
                  simp at hu
            subst ss
            cases as with
            | nil =>
                have hv := congrArg (fun t => (GapTree.rootLabel t).val) hsource
                simp [tree, cnfLabel, GapTree.label0, GapTree.label1] at hv
            | cons a as =>
                have hchildren := congrArg GapTree.children hsource
                simp [tree, treeList] at hchildren
          · obtain ⟨u, hu, hsub⟩ := hdesc
            simp at hu
      | theta b =>
          cases as with
          | nil => exact Or.inl FreundTerm_lt.cnf_nil_theta
          | cons a as =>
              have haNormal : FreundTerm_normal a :=
                FreundTermList_normal_head has
              have haMem : a ∈ a :: as := by simp
              have haCmplx : complexity a < complexity (.cnf (a :: as)) :=
                complexity_lt_cnf_of_mem haMem
              have haSource : GapTreeEmbeds (tree a) (tree (.cnf (a :: as))) :=
                tree_mem_embeds_cnf has haMem
              have haTarget : GapTreeEmbeds (tree a) (tree (.theta b)) :=
                GapTreeEmbeds_trans haSource h
              have haLe : a ≤f .theta b :=
                tree_embedding_le haNormal hb haTarget
              have hheadSize := tree_head_transComplexity_lt_cnf a as
              have hwholeSize := GapTreeEmbeds_transComplexity_le h
              have haLt : a <f .theta b := by
                rcases haLe with hlt | heq
                · exact hlt
                · subst a
                  omega
              exact Or.inl (FreundTerm_lt.cnf_theta haLt)
      | cnf bs =>
          cases hb with
          | cnf hbs hsingleB =>
            have hnode : GapTreeEmbeds (tree (.cnf as)) (.node (cnfLabel bs) (treeList bs)) := by
              simpa [tree] using h
            rcases GapTreeEmbeds_to_node_cases hnode with hroot | hdesc
            · obtain ⟨ss, hsource, hforest⟩ := hroot
              have hchildren := congrArg GapTree.children hsource
              have hss : ss = treeList as := by
                simpa [tree] using hchildren.symm
              subst ss
              have hlist : as ≤fl bs := treeList_embedding_le has hbs hforest
              rcases hlist with hlt | heq
              · exact Or.inl (FreundTerm_lt.cnf_cnf hlt)
              · subst bs
                exact Or.inr rfl
            · obtain ⟨u, hu, hsub⟩ := hdesc
              obtain ⟨c, hc, hcu⟩ := mem_treeList_iff.mp hu
              subst u
              have hcNormal : FreundTerm_normal c :=
                FreundTermList_normal_mem hbs c hc
              have hcCmplx : complexity c < complexity (.cnf bs) :=
                complexity_lt_cnf_of_mem hc
              have hSourceC : (.cnf as : FreundTerm) ≤f c :=
                tree_embedding_le
                  (FreundTerm_normal.cnf has hsingle)
                  hcNormal
                  hsub
              cases bs with
              | nil => simp at hc
              | cons b bs =>
                  have hcb : c ≤f b := by
                    simp only [List.mem_cons] at hc
                    rcases hc with rfl | hc
                    · exact Or.inr rfl
                    · exact
                        FreundTermList_normal_tail_bounded hbs c hc
                  have hSourceHead : (.cnf as : FreundTerm) ≤f b :=
                    FreundTerm_le_trans hSourceC hcb
                  exact Or.inl
                    (FreundTerm_lt_of_le_of_lt
                      hSourceHead
                      (FreundTerm_lt_cnf_cons_self
                        b bs))


termination_by
  complexity a + complexity b
decreasing_by
  all_goals
    subst_vars
    try simp [complexity, complexityList] at hγCmplx
    try simp [complexity, complexityList] at hcCmplx
    try simp [complexity, complexityList] at haCmplx
    simp [complexity, complexityList]
    omega


/-- Forest embedding of encoded normal CNF lists reflects the lexicographic order. -/
theorem treeList_embedding_le {as bs : List FreundTerm} (has : FreundTermList_normal as)
        (hbs : FreundTermList_normal bs) (h : GapForestEmbeds (treeList as) (treeList bs)) :
        as ≤fl bs := by
  cases as with
  | nil =>
      cases bs with
      | nil => exact Or.inr rfl
      | cons b bs => exact Or.inl FreundTermList_lt.nil
  | cons a as =>
      cases bs with
      | nil =>
          have haMem : tree a ∈ treeList (a :: as) := by
            simp [treeList]
          obtain ⟨u, hu, _⟩ := GapForestEmbeds_exists_of_mem h haMem
          simp at hu
      | cons b bs =>
          have haNormal : FreundTerm_normal a := FreundTermList_normal_head has
          have hbNormal : FreundTerm_normal b := FreundTermList_normal_head hbs
          have hasTail : FreundTermList_normal as := FreundTermList_normal_tail has
          have hbsTail : FreundTermList_normal bs := FreundTermList_normal_tail hbs
          obtain ⟨c, hc, hac⟩ := treeList_embedding_head h
          have hcNormal : FreundTerm_normal c :=
            FreundTermList_normal_mem hbs c hc
          have hcCmplx : complexity c < complexity (.cnf (b :: bs)) :=
            complexity_lt_cnf_of_mem hc
          have hacLe : a ≤f c := tree_embedding_le haNormal hcNormal hac
          have hcb : c ≤f b := by
            simp only [List.mem_cons] at hc
            rcases hc with rfl | hc
            · exact Or.inr rfl
            · exact FreundTermList_normal_tail_bounded hbs c hc
          have hab : a ≤f b := FreundTerm_le_trans hacLe hcb
          rcases hab with hab | hab
          · exact Or.inl (FreundTermList_lt.head hab)
          · subst b
            have hcancel : GapForestEmbeds (treeList as) (treeList bs) := by
              change GapForestEmbeds (tree a :: treeList as) (tree a :: treeList bs) at h
              exact GapForestEmbeds_cancel_head h
            have htail : as ≤fl bs :=
              treeList_embedding_le hasTail hbsTail hcancel
            rcases htail with htail | htail
            · exact Or.inl (FreundTermList_lt.tail htail)
            · subst bs
              exact Or.inr rfl
termination_by complexityList as + complexityList bs
decreasing_by
  all_goals
    subst_vars
    try simp [complexity, complexityList] at hcCmplx
    simp [complexity, complexityList]
    omega
end
end FreundTerm



def NormalFreundTerm_le (a b : NormalFreundTerm) : Prop := a.1 ≤f b.1

instance NormalFreundTerm_le_isPreorder : IsPreorder NormalFreundTerm NormalFreundTerm_le where
  refl := by intro a; exact Or.inr rfl
  trans := by intro a b c hab hbc; exact FreundTerm.FreundTerm_le_trans hab hbc

theorem NormalFreundTerm_le_wqo (hGap : WellQuasiOrdered GapTreeEmbeds) :
        WellQuasiOrdered NormalFreundTerm_le := by
  intro f
  obtain ⟨i, j, hij, hTree⟩ := hGap (fun n => FreundTerm.tree (f n).1)
  refine ⟨i, j, hij, ?_⟩
  exact FreundTerm.tree_embedding_le (f i).2 (f j).2 hTree

def NormalFreundTerm_strict (a b : NormalFreundTerm) : Prop :=
  NormalFreundTerm_le a b ∧ ¬ NormalFreundTerm_le b a

theorem NormalFreundTerm_strict_wf (hGap : WellQuasiOrdered GapTreeEmbeds) :
    WellFounded NormalFreundTerm_strict := by
  simpa [NormalFreundTerm_strict] using (NormalFreundTerm_le_wqo hGap).wellFounded

def NormalFreundTerm_lt (a b : NormalFreundTerm) : Prop := a.1 <f b.1

namespace FreundTerm
theorem E_mem_is_theta {a g : FreundTerm} (hg : g ∈ FreundTerm.E a) : ∃ b, g = .theta b := by
  cases a with
  | Omega => simp [FreundTerm.E] at hg
  | theta a => simp [FreundTerm.E] at hg; subst g; exact ⟨a, rfl⟩
  | cnf as =>
    change g ∈ FreundTerm.EList as at hg
    obtain ⟨c, hc, hgc⟩ := EList_mem_exists hg
    exact E_mem_is_theta hgc

theorem E_mem_lt_theta {a g : FreundTerm} (hg : g ∈ FreundTerm.E a) : g <f .theta a := by
  obtain ⟨b, rfl⟩ := E_mem_is_theta hg
  exact FreundTerm_lt.theta_theta_support_eq hg

mutual
theorem FreundTerm_lt_irrefl (a : FreundTerm) : ¬ a <f a := by
  intro h -- a <f a
  cases a with
  | Omega => cases h
  | theta a =>
    cases h with
    | theta_theta_forward haa => exact FreundTerm_lt_irrefl a haa
    -- ∀ g ∈ theta b, theta a < g → theta a < theta b
    | @theta_theta_support_lt _ _ g hg hTg =>
      have hgCmplx : FreundTerm.complexity g < FreundTerm.complexity (.theta a) :=
        E_mem_complexity_lt_theta hg
      have hgT : g <f (.theta a : FreundTerm) := E_mem_lt_theta hg
      have hgg : g <f g := FreundTerm_lt_trans hgT hTg
      exact FreundTerm_lt_irrefl g hgg
    -- if theta a < E b then theta a < theta b
    | theta_theta_support_eq hg =>
      have hcmplx : FreundTerm.complexity (.theta a) < FreundTerm.complexity (.theta a) :=
        E_mem_complexity_lt_theta hg
      omega
  | cnf as => cases h with
              | cnf_cnf hlist =>
                exact FreundTermList_lt_irrefl as hlist
  termination_by FreundTerm.complexity a
  decreasing_by
    all_goals
      subst_vars
      try simp [FreundTerm.complexity] at *
      try omega
theorem FreundTermList_lt_irrefl (as : List FreundTerm) : ¬ FreundTermList_lt as as := by
  intro h
  cases as with
  | nil => cases h
  | cons a as =>
    cases h with
    | head haa => exact FreundTerm_lt_irrefl a haa
    | tail htail => exact FreundTermList_lt_irrefl as htail
  termination_by
    FreundTerm.complexityList as
  decreasing_by
    all_goals
      subst_vars
      simp [FreundTerm.complexity,FreundTerm.complexityList]
      try omega
end
end FreundTerm

theorem NormalFreundTerm_lt_to_strict {a b : NormalFreundTerm} (hab : NormalFreundTerm_lt a b) :
        NormalFreundTerm_strict a b := by
  change a.1 <f b.1 at hab
  constructor
  · exact Or.inl hab
  · intro hba
    change b.1 ≤f a.1 at hba
    rcases hba with hba | hba
    · have haa : a.1 <f a.1 :=
        FreundTerm.FreundTerm_lt_trans hab hba
      exact FreundTerm.FreundTerm_lt_irrefl a.1 haa
    · rw [hba] at hab
      exact FreundTerm.FreundTerm_lt_irrefl a.1 hab

theorem NormalFreundTerm_lt_wf (hGap : WellQuasiOrdered GapTreeEmbeds) :
        WellFounded NormalFreundTerm_lt := by
  apply (NormalFreundTerm_strict_wf hGap).mono
  intro a b hab
  exact NormalFreundTerm_lt_to_strict hab

--========================================================================================
-- Conversion of FreundTerm to our Notations

namespace FreundTerm
-- FreundTerm as its ω-CNF exponent list
def cnfExponents : FreundTerm → List FreundTerm
  | .Omega => [.Omega]
  | .theta a => [.theta a]
  | .cnf as => as
def packCNF : List FreundTerm → FreundTerm
  | [] => .cnf []
  | [.Omega] => .Omega
  | [.theta a] => .theta a
  | [.cnf as] => .cnf [.cnf as]
  | a :: b :: rest => .cnf (a :: b :: rest)
@[simp]
theorem cnfExponents_packCNF (as : List FreundTerm) : cnfExponents (packCNF as) = as := by
  cases as with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil =>
      cases a with
      | Omega => simp [packCNF, cnfExponents]
      | theta a => simp [packCNF, cnfExponents]
      | cnf cs => rfl
    | cons b bs => simp [packCNF, cnfExponents]
@[simp]
theorem packCNF_cnfExponents_of_normal {a : FreundTerm} (ha : FreundTerm_normal a) :
        packCNF (cnfExponents a) = a := by
  cases a with
  | Omega => rfl
  | theta a => rfl
  | cnf as =>
    cases ha with
    | cnf has hsingle =>
      cases as with
      | nil => rfl
      | cons a rest =>
        cases rest with
        | nil => have hok : FreundSingletonOK a := hsingle a rfl
                 cases a with
                 | Omega => simp [FreundSingletonOK] at hok
                 | theta b => simp [FreundSingletonOK] at hok
                 | cnf bs => simp [cnfExponents, packCNF]
        | cons b rest => simp [cnfExponents, packCNF]
end FreundTerm
namespace BHToFreund
-- Translate principal to Freund, assuming we know how to omegaTerm with F
def principalWith (F : omegaTerm → FreundTerm) : principal → FreundTerm
  | .psi a => .theta (F a)
def principalListWith (F : omegaTerm → FreundTerm) : List principal → List FreundTerm
  | [] => []
  | p :: ps => principalWith F p :: principalListWith F ps
def countableWith (F : omegaTerm → FreundTerm) : countableOrd → FreundTerm
  | .sum ps => FreundTerm.packCNF (principalListWith F ps)
@[simp]
theorem principalWith_psi (F : omegaTerm → FreundTerm) (a : omegaTerm) :
        principalWith F (.psi a) = .theta (F a) := by rfl
@[simp]
theorem principalListWith_nil (F : omegaTerm → FreundTerm) :
        principalListWith F [] = [] := by rfl
@[simp]
theorem principalListWith_cons (F : omegaTerm → FreundTerm) (p : principal) (ps : List principal) :
        principalListWith F (p :: ps) = principalWith F p :: principalListWith F ps := by rfl
@[simp]
theorem countableWith_sum (F : omegaTerm → FreundTerm) (ps : List principal) :
        countableWith F (.sum ps) = FreundTerm.packCNF (principalListWith F ps) := by rfl
@[simp]
theorem countableWith_zero (F : omegaTerm → FreundTerm) :
        countableWith F countableOrd.zero = .cnf [] := by
  simp [countableOrd.zero, countableWith, principalListWith, FreundTerm.packCNF]
@[simp]
theorem countableWith_ofPrincipal (F : omegaTerm → FreundTerm) (p : principal) :
        countableWith F (countableOrd.ofPrincipal p) = principalWith F p := by
  cases p with
  | psi a =>
      simp [countableOrd.ofPrincipal, countableWith, principalListWith,
            principalWith, FreundTerm.packCNF]
@[simp]
theorem cnfExponents_countableWith (F : omegaTerm → FreundTerm) (ps : List principal) :
        FreundTerm.cnfExponents (countableWith F (.sum ps)) = principalListWith F ps := by
  simp [countableWith]
end BHToFreund
namespace FreundTerm
-- Fruend's ordinal addition
-- Keep initial segment whose exponents are at least b
noncomputable def keepGE (b : FreundTerm) (as : List FreundTerm) : List FreundTerm := by
  classical
  exact match as with
        | [] => []
        | a :: rest => if b ≤f a then a :: keepGE b rest
                       else []
-- For (ω^α + ω^β) + ω^γ drops the final exponents of the left side with <c
noncomputable def cnfAdd (a b : FreundTerm) : FreundTerm := by
  classical
  exact
    match cnfExponents b with
    | [] => a
    | c :: cs => packCNF (keepGE c (cnfExponents a) ++ (c :: cs))
-- Freund's ordinal multiplication
-- If a = ω^α₀ + ... + ω^{α_n} then Ωa = ω^{Ω+α₀} + ... + ω^{Ω+α_n}
noncomputable def OmegaMul (a : FreundTerm) : FreundTerm :=
  packCNF ((cnfExponents a).map (fun e => cnfAdd .Omega e))
noncomputable def shiftExponents (base beta : FreundTerm) :
    List FreundTerm := (cnfExponents beta).map (fun p => cnfAdd base p)
end FreundTerm
-- The actual translation from BH notation to FreundTerm
namespace BHToFreund
mutual
noncomputable def countable : _root_.countableOrd → FreundTerm
  | .sum ps => FreundTerm.packCNF (principalList ps)
noncomputable def principal : _root_.principal → FreundTerm
  | .psi a => .theta (omega a)
noncomputable def principalList : List _root_.principal → List FreundTerm
  | [] => []
  | p :: ps => principal p :: principalList ps
noncomputable def omega : _root_.omegaTerm → FreundTerm
  | .zero => .cnf []
  | .omegaNF alpha beta gamma =>
      let base := FreundTerm.OmegaMul (omega alpha)
      FreundTerm.packCNF (FreundTerm.shiftExponents base (countable beta)
          ++ FreundTerm.cnfExponents (omega gamma))
end
@[simp]
theorem countable_sum (ps : List _root_.principal) :
  countable (.sum ps) = FreundTerm.packCNF (principalList ps) := by rfl
@[simp]
theorem principal_psi (a : _root_.omegaTerm) : principal (.psi a) = .theta (omega a) := by rfl
@[simp]
theorem principalList_nil : principalList [] = [] := by rfl
@[simp]
theorem principalList_cons (p : _root_.principal) (ps : List _root_.principal) :
        principalList (p :: ps) = principal p :: principalList ps := by rfl
@[simp]
theorem omega_zero : omega (.zero : _root_.omegaTerm) = (.cnf [] : FreundTerm) := by rfl
@[simp]
theorem omega_omegaNF (alpha gamma : _root_.omegaTerm) (beta : _root_.countableOrd) :
        omega (.omegaNF alpha beta gamma) =
        FreundTerm.packCNF (FreundTerm.shiftExponents (FreundTerm.OmegaMul (omega alpha))
          (countable beta)
          ++
          FreundTerm.cnfExponents (omega gamma)) := by rfl
@[simp]
theorem countable_zero : countable _root_.countableOrd.zero = (.cnf [] : FreundTerm) := by
  simp [_root_.countableOrd.zero, countable, principalList, FreundTerm.packCNF]
@[simp]
theorem countable_ofPrincipal (p : _root_.principal) :
    countable (_root_.countableOrd.ofPrincipal p) = principal p := by
  cases p with
  | psi a =>
      simp [_root_.countableOrd.ofPrincipal, countable, principalList, principal,
            FreundTerm.packCNF]
@[simp]
theorem cnfExponents_countable_sum (ps : List _root_.principal) :
        FreundTerm.cnfExponents (countable (.sum ps)) = principalList ps := by
  simp [countable]
-- BH equality and LEAN equality
mutual
theorem countableOrd_eq_to_eq {a b : countableOrd} (h : a=cb) : a = b := by
  cases h with
  | sum hList =>
      exact congrArg countableOrd.sum (principalList_eq_to_eq hList)
theorem principal_eq_to_eq {p q : _root_.principal} (h : p =p q) : p = q := by
  cases h with
  | psi hArg =>
      exact congrArg principal.psi (omegaTerm_eq_to_eq hArg)
theorem principalList_eq_to_eq {ps qs : List _root_.principal} (h : principalList_eq ps qs) :
        ps = qs := by
  cases h with
  | nil => rfl
  | cons hHead hTail =>
      rw [principal_eq_to_eq hHead, principalList_eq_to_eq hTail]
theorem omegaTerm_eq_to_eq {a b : omegaTerm} (h : a =o b) : a = b := by
  cases h with
  | zero => rfl
  | omegaNF hAlpha hBeta hGamma =>
      rw [omegaTerm_eq_to_eq hAlpha, countableOrd_eq_to_eq hBeta, omegaTerm_eq_to_eq hGamma]
end
-- Custom equality of countable ordinals is preserved by the translation to Freund terms.
theorem countable_eq_map_eq {a b : countableOrd} (h : a=cb) : countable a = countable b := by
  rw [countableOrd_eq_to_eq h]
-- Custom equality of principal terms is preserved by the translation to Freund terms.
theorem principal_eq_map_eq {p q : _root_.principal} (h : p=pq) : principal p = principal q := by
  rw [principal_eq_to_eq h]
-- Custom equality of principal lists is preserved by the translation to Freund-term lists.
theorem principalList_eq_map_eq {ps qs : List _root_.principal} (h : principalList_eq ps qs) :
        principalList ps = principalList qs := by
  rw [principalList_eq_to_eq h]
-- Custom equality of Ω-terms is preserved by the translation to Freund terms.
theorem omega_eq_map_eq {a b : omegaTerm} (h : a=ob) : omega a = omega b := by
  rw [omegaTerm_eq_to_eq h]
end BHToFreund
namespace FreundTerm
theorem packCNF_normal {as : List FreundTerm} (has : FreundTermList_normal as) :
        FreundTerm_normal (packCNF as) := by
  cases as with
  | nil =>
    have h : FreundTerm_normal (.cnf []) := by
        apply FreundTerm_normal.cnf
        · exact FreundTermList_normal.nil
        · intro x hx
          simp at hx
    simpa [packCNF] using h
  | cons a rest =>
    cases rest with
      | nil =>
        cases has with
        | single ha =>
          cases a with
          | Omega => simpa [packCNF] using ha
          | theta b => simpa [packCNF] using ha
          | cnf bs =>
            have h : FreundTerm_normal (.cnf [(.cnf bs : FreundTerm)]) := by
              apply FreundTerm_normal.cnf
              · exact FreundTermList_normal.single ha
              · intro x hx
                have hx' : x = (.cnf bs : FreundTerm) := by
                  simpa using hx.symm
                subst x
                simp [FreundSingletonOK]
            simpa [packCNF] using h
      | cons b rest =>
        have h : FreundTerm_normal (.cnf (a :: b :: rest)) := by
          apply FreundTerm_normal.cnf
          · exact has
          · intro x hx; simp at hx
        simpa [packCNF] using h
end FreundTerm
namespace BHToFreund
@[simp]
theorem principalList_eq_map (ps : List _root_.principal) :
        principalList ps = ps.map principal := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [principalList, ih]
theorem principalList_normal_map_of (hPrincipalNormal : ∀ {p : _root_.principal},
        principal_normal p → FreundTerm_normal (principal p))
        (hPrincipalLe : ∀ {p q : _root_.principal}, p≤pq → principal p ≤f principal q)
        {ps : List _root_.principal} (hps : principalList_normal ps) :
        FreundTermList_normal (principalList ps) := by
  cases ps with
  | nil => exact FreundTermList_normal.nil
  | cons p ps =>
      cases ps with
      | nil =>
          -- source list is [p]
          cases hps with
          | singleton hp =>
              simp only [principalList]
              exact FreundTermList_normal.single
                (hPrincipalNormal hp)
      | cons q qs =>
          -- source list is p :: q :: qs
          cases hps with
          | cons hp htail hpq =>
              simp only [principalList]
              apply FreundTermList_normal.cons
              · exact hPrincipalNormal hp
              · exact principalList_normal_map_of
                  hPrincipalNormal
                  hPrincipalLe
                  htail
              · intro t ht
                have ht' : t ∈ principalList (q :: qs) := by
                  simpa only [principalList] using ht
                rw [principalList_eq_map] at ht'
                obtain ⟨r, hr, hrt⟩ := List.mem_map.mp ht'
                subst t
                have hwhole : principalList_normal (p :: q :: qs) :=
                  principalList_normal.cons hp htail hpq
                have hrp : r ≤p p :=
                  principalList_normal_tail_bounded hwhole r hr
                exact hPrincipalLe hrp

theorem countable_normal_map_of (hPrincipalNormal : ∀ {p : _root_.principal}, principal_normal p →
        FreundTerm_normal (principal p))
        (hPrincipalLe : ∀ {p q : _root_.principal}, p≤pq → principal p ≤f principal q)
        {a : _root_.countableOrd} (ha : countableOrd_normal a) :
        FreundTerm_normal (countable a) := by
  cases ha with
  | sum hps =>
      rw [countable_sum]
      apply FreundTerm.packCNF_normal
      exact principalList_normal_map_of
        hPrincipalNormal
        hPrincipalLe
        hps
-- if normal Ω-terms map to normal Freund terms, then normal principals automatically do too
theorem principal_normal_map_of
        (hOmegaNormal : ∀ {a : _root_.omegaTerm}, omegaTerm_normal a → FreundTerm_normal (omega a))
        {p : _root_.principal} (hp : principal_normal p) :
        FreundTerm_normal (principal p) := by
  cases hp with
  | psi harg hcoeff =>
      rw [principal_psi]
      exact FreundTerm_normal.theta (hOmegaNormal harg)
-- If strict principal order maps to <f, then weak principal order maps to ≤f.
theorem principal_le_map_of_lt
        (hPrincipalLt : ∀ {p q : _root_.principal}, p<pq → principal p <f principal q)
        {p q : _root_.principal} (h : p≤pq) :
        principal p ≤f principal q := by
  rcases h with hlt | heq
  · exact Or.inl (hPrincipalLt hlt)
  · exact Or.inr (principal_eq_map_eq heq)
/- Normal countable ordinals map to normal Freund terms once Ω-term normality and strict
   principal-order preservation are known. -/
theorem countable_normal_map_of_omega_lt
        (hOmegaNormal : ∀ {a : _root_.omegaTerm}, omegaTerm_normal a → FreundTerm_normal (omega a))
        (hPrincipalLt : ∀ {p q : _root_.principal}, p<pq → principal p <f principal q)
        {a : _root_.countableOrd} (ha : countableOrd_normal a) :
        FreundTerm_normal (countable a) := by
  apply countable_normal_map_of
  · intro p hp
    exact principal_normal_map_of hOmegaNormal hp
  · intro p q hpq
    exact principal_le_map_of_lt hPrincipalLt hpq
  · exact ha
/- Strict comparison of our principal list is preserved by the Freund trenalation, assuming
   strict prinicpal comparison is preserved. -/
theorem principalList_lt_map_of
        (hPrincipalLt : ∀ {p q : _root_.principal}, p<pq → principal p <f principal q)
        {ps qs : List _root_.principal} (h : principalList_lt ps qs) :
        FreundTermList_lt (principalList ps) (principalList qs) := by
  cases h with
  | nil => simp only [principalList]; exact FreundTermList_lt.nil
  | head hpq => simp only [principalList]
                exact FreundTermList_lt.head (hPrincipalLt hpq)
  | tail hpq htail =>
      simp only [principalList]
      have hhead : principal _ = principal _ := principal_eq_map_eq hpq
      rw [hhead]
      exact FreundTermList_lt.tail (principalList_lt_map_of hPrincipalLt htail)
-- A strict comparison of source principal lists remains strict
-- after packing their translated lists into canonical Freund terms.
theorem principalList_pack_lt_map_of
        (hPrincipalLt : ∀ {p q : _root_.principal}, p<pq → principal p <f principal q)
        {ps qs : List _root_.principal} (h : principalList_lt ps qs) :
        FreundTerm.packCNF (principalList ps) <f FreundTerm.packCNF (principalList qs) := by
  cases h with
  | @nil p ps =>
    cases p with
    | psi a =>
      cases ps with
      -- [] < [ψ(a)]
      -- becomes 0 < θ(F(a))
      | nil =>
        simpa only [principalList, principal, FreundTerm.packCNF] using
          (FreundTerm_lt.cnf_nil_theta (b := omega a))
      -- [] < ψ(a) :: q :: qs
      -- both sides are now genuine CNFs
      | cons q qs =>
        have h0 : (.cnf [] : FreundTerm) <f
                    .cnf (principal (.psi a) :: principal q :: principalList qs) :=
          FreundTerm_lt.cnf_cnf FreundTermList_lt.nil
        simpa only [principalList, FreundTerm.packCNF ] using h0
  -- p < q at the first differing position
  | @head p q ps qs hpq =>
    have hpqF : principal p <f principal q := hPrincipalLt hpq
    cases p with
    | psi a =>
      cases q with
      | psi b =>
        change (.theta (omega a) : FreundTerm) <f .theta (omega b) at hpqF
        cases ps with
        | nil =>
          cases qs with
          -- [p] < [q]
          | nil =>
            simpa only [principalList, principal, FreundTerm.packCNF] using hpqF
          -- [p] < q :: r :: rs
          | cons r rs =>
            have hout : (.theta (omega a) : FreundTerm) <f
                         .cnf ((.theta (omega b) : FreundTerm) :: principal r ::
                         principalList rs) := FreundTerm_lt.theta_cnf_lt hpqF
            simpa only [ principalList, principal, FreundTerm.packCNF] using hout
        | cons r rs =>
          cases qs with
          -- p :: r :: rs < [q]
          | nil =>
            have hout : (.cnf ((.theta (omega a) : FreundTerm) :: principal r ::
                          principalList rs)) <f .theta (omega b) :=
                    FreundTerm_lt.cnf_theta hpqF
            simpa only [principalList, principal, FreundTerm.packCNF] using hout
              -- both have at least two elements
          | cons s ss =>
            have hlist : FreundTermList_lt ((.theta (omega a) : FreundTerm) ::
                         principal r :: principalList rs) ((.theta (omega b) : FreundTerm) ::
                         principal s :: principalList ss) := FreundTermList_lt.head hpqF
            have hout : (.cnf ((.theta (omega a) : FreundTerm) :: principal r ::
                        principalList rs)) <f
                        .cnf ((.theta (omega b) : FreundTerm) :: principal s ::
                        principalList ss) :=
              FreundTerm_lt.cnf_cnf hlist
            simpa only [principalList, principal, FreundTerm.packCNF ] using hout
  -- equal heads, comparison occurs later
  | @tail p q ps qs hpq htail =>
    have hfull : FreundTermList_lt (principalList (p :: ps)) (principalList (q :: qs)) :=
      principalList_lt_map_of hPrincipalLt (principalList_lt.tail hpq htail)
    have hpqLean : p = q := principal_eq_to_eq hpq
    subst q
    cases p with
    | psi a =>
      cases ps with
      -- left side is the singleton [ψ(a)]
      | nil =>
        cases qs with
        -- impossible: [] < []
        | nil =>
          cases htail
          -- [ψ(a)] < ψ(a) :: r :: rs
          | cons r rs =>
            have hout : (.theta (omega a) : FreundTerm) <f
                        .cnf ((.theta (omega a) : FreundTerm) ::
                         principal r :: principalList rs) :=
              FreundTerm_lt.theta_cnf_eq
            simpa only [principalList, principal, FreundTerm.packCNF] using hout
          -- left side has at least two entries
       | cons r rs =>
         cases qs with
         -- impossible: nonempty < []
         | nil =>
           cases htail
           -- both become genuine CNFs
           | cons s ss =>
             have hout : (.cnf ((.theta (omega a) : FreundTerm) ::
                         principal r :: principalList rs)) <f
                         .cnf ((.theta (omega a) : FreundTerm) ::
                         principal s :: principalList ss) :=
               FreundTerm_lt.cnf_cnf hfull
             simpa only [principalList, principal, FreundTerm.packCNF] using hout
theorem countable_lt_map_of
        (hPrincipalLt : ∀ {p q : _root_.principal}, p<pq → principal p <f principal q)
        {a b : _root_.countableOrd} (h : a<cb) : countable a <f countable b := by
  cases h with
  | sum hlist =>
      exact principalList_pack_lt_map_of hPrincipalLt hlist
end BHToFreund
namespace FreundTerm
-- EList distributes over concatenation of CNF exponent lists.
@[simp]
theorem EList_append (as bs : List FreundTerm) :
        EList (as ++ bs) = EList as ++ EList bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [EList, ih, List.append_assoc]
-- Packing an exponent list into canonical Freund syntax does not
-- change its set/list of critical θ-terms.
@[simp]
theorem E_packCNF (as : List FreundTerm) : E (packCNF as) = EList as := by
  cases as with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil =>
      cases a with
      | Omega => simp [packCNF, E, EList]
      | theta b => simp [packCNF, E, EList]
      | cnf bs => simp [packCNF, E, EList]
    | cons b bs =>
      simp [packCNF, E, EList, List.append_assoc]
theorem mem_EList_append_iff {as bs : List FreundTerm} {g : FreundTerm} :
        g ∈ EList (as ++ bs) ↔ g ∈ EList as ∨ g ∈ EList bs := by
  rw [EList_append]; simp
@[simp]
theorem EList_cnfExponents (a : FreundTerm) : EList (cnfExponents a) = E a := by
  cases a with
  | Omega => rfl
  | theta a => simp [cnfExponents, EList, E]
  | cnf as => rfl
-- Adding Ω on the left does not introduce any new critical θ-terms.
@[simp]
theorem E_cnfAdd_Omega (b : FreundTerm) : E (cnfAdd .Omega b) = E b := by
  classical
  cases h : cnfExponents b with
  | nil =>
    calc
    E (cnfAdd .Omega b) = E (.Omega : FreundTerm) := by
      simp [cnfAdd, h]
    _ = [] := by  rfl
    _ = EList (cnfExponents b) := by rw [h]; rfl
    _ = E b := by exact EList_cnfExponents b
  | cons c cs =>
    have hkeep : EList (keepGE c (cnfExponents (.Omega : FreundTerm))) = [] := by
      by_cases hc : c ≤f .Omega
      · simp [cnfExponents, keepGE, EList, E, hc]
      · simp [cnfExponents, keepGE, EList, hc]
    calc
      E (cnfAdd .Omega b) =
      EList (keepGE c (cnfExponents (.Omega : FreundTerm)) ++ (c :: cs)) := by
        simp [cnfAdd, h, E_packCNF]
      _ = EList (c :: cs) := by
            rw [EList_append, hkeep]
            simp
      _ = EList (cnfExponents b) := by rw [h]
      _ = E b := by exact EList_cnfExponents b
-- Applying Ω + _ to every exponent preserves the total critical-term list.
@[simp]
theorem EList_map_cnfAdd_Omega (as : List FreundTerm) :
        EList (as.map (fun e => cnfAdd .Omega e)) = EList as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [EList, ih]
-- Multiplication by Ω preserves the critical θ-terms.
@[simp]
theorem E_OmegaMul (a : FreundTerm) : E (OmegaMul a) = E a := by
  simp [OmegaMul]
-- Every critical term of base + a comes either from base or from a.
theorem E_cnfAdd_subset {base a g : FreundTerm} (hg : g ∈ E (cnfAdd base a)) :
        g ∈ E base ∨ g ∈ E a := by
  classical
  have hkeep : ∀ (c : FreundTerm) (as : List FreundTerm),
      g ∈ EList (keepGE c as) → g ∈ EList as := by
    intro c as
    induction as with
    | nil => simp [keepGE, EList]
    | cons d ds ih =>
      by_cases hcd : c ≤f d
      · intro hmem
        simp only [keepGE, hcd, ↓reduceIte, EList, List.mem_append] at hmem ⊢
        rcases hmem with hd | hds
        · exact Or.inl hd
        · exact Or.inr (ih hds)
      · simp [keepGE, EList, hcd]
  cases h : cnfExponents a with
  | nil =>
    left
    simpa [cnfAdd, h] using hg
  | cons c cs =>
    have hg' : g ∈ EList (keepGE c (cnfExponents base) ++ (c :: cs)) := by
      simpa [cnfAdd, h] using hg
    rw [mem_EList_append_iff] at hg'
    rcases hg' with hgbase | hga
    · left
      rw [← EList_cnfExponents base]
      exact hkeep c (cnfExponents base) hgbase
    · right
      rw [← EList_cnfExponents a, h]
      exact hga
-- Every critical term of the right summand survives ordinal addition.
theorem E_right_mem_cnfAdd {base a g : FreundTerm} (hg : g ∈ E a) :
        g ∈ E (cnfAdd base a) := by
  classical
  cases h : cnfExponents a with
  | nil =>
    have : g ∈ EList (cnfExponents a) := by
      simpa using hg
    rw [h] at this
    simp [EList] at this
  | cons c cs =>
    have hg' : g ∈ EList (c :: cs) := by
      rw [← h]
      simpa using hg
    have : g ∈ EList (keepGE c (cnfExponents base) ++ (c :: cs)) :=
      mem_EList_append_iff.mpr (Or.inr hg')
    simpa [cnfAdd, h] using this
-- Critical terms of shifted exponents come from the base or the coefficient.
theorem EList_shiftExponents_subset {base beta g : FreundTerm}
        (hg : g ∈ EList (shiftExponents base beta)) :
        g ∈ E base ∨ g ∈ E beta := by
  have hmap : ∀ (as : List FreundTerm),
      g ∈ EList (as.map (fun p => cnfAdd base p)) →
        g ∈ E base ∨ g ∈ EList as := by
    intro as
    induction as with
    | nil => simp [EList]
    | cons a as ih =>
      simp only [List.map_cons, EList, List.mem_append] at *
      intro h
      rcases h with ha | has
      · rcases E_cnfAdd_subset ha with hbase | ha
        · exact Or.inl hbase
        · exact Or.inr (Or.inl ha)
      · rcases ih has with hbase | has
        · exact Or.inl hbase
        · exact Or.inr (Or.inr has)
  rcases hmap (cnfExponents beta) (by simpa [shiftExponents] using hg) with
    hbase | hbeta
  · exact Or.inl hbase
  · exact Or.inr (by simpa using hbeta)
end FreundTerm

namespace BHToFreund
-- A source principal in a countable ordinal occurs as an exponent of its translation.
theorem principal_mem_countable_exponents {p : _root_.principal}
        {ps : List _root_.principal} (hp : p ∈ ps) :
        principal p ∈ FreundTerm.cnfExponents (countable (.sum ps)) := by
  rw [cnfExponents_countable_sum, principalList_eq_map]
  exact List.mem_map.mpr ⟨p, hp, rfl⟩
-- Every exponent of a translated countable ordinal comes from a source principal.
theorem countable_exponent_exists_principal {c : _root_.countableOrd} {g : FreundTerm}
        (hg : g ∈ FreundTerm.cnfExponents (countable c)) :
        ∃ p ps, c = .sum ps ∧ p ∈ ps ∧ g = principal p := by
  cases c with
  | sum ps =>
    rw [cnfExponents_countable_sum, principalList_eq_map] at hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    exact ⟨p, ps, rfl, hp, rfl⟩
-- Every critical term of omega a comes from a principal component of a source coefficient.
theorem E_omega_exists_coefficient {a : _root_.omegaTerm} {g : FreundTerm}
        (hg : g ∈ FreundTerm.E (omega a)) :
        ∃ c, c ∈ omegaTerm.coefficients a ∧
        ∃ p ps, c = .sum ps ∧ p ∈ ps ∧ g = principal p := by
  cases a with
  | zero => simp [omega_zero, FreundTerm.E, FreundTerm.EList] at hg
  | omegaNF alpha beta gamma =>
    rw [omega_omegaNF, FreundTerm.E_packCNF,
        FreundTerm.EList_append] at hg
    simp only [List.mem_append] at hg
    rcases hg with hshift | hgamma
    · rcases FreundTerm.EList_shiftExponents_subset hshift with halpha | hbeta
      · rw [FreundTerm.E_OmegaMul] at halpha
        obtain ⟨c, hc, p, ps, hcform, hp, hgp⟩ :=
          E_omega_exists_coefficient halpha
        exact ⟨c, by simp [omegaTerm.coefficients, hc], p, ps, hcform, hp, hgp⟩
      · rw [← FreundTerm.EList_cnfExponents] at hbeta
        obtain ⟨e, he, hge⟩ := FreundTerm.EList_mem_exists hbeta
        obtain ⟨p, ps, rfl, hp, rfl⟩ := countable_exponent_exists_principal he
        have hgp : g = principal p := by
          cases p with
          | psi d => simpa [principal, FreundTerm.E] using hge
        exact ⟨.sum ps, by simp [omegaTerm.coefficients], p, ps, rfl, hp, hgp⟩
    · rw [FreundTerm.EList_cnfExponents] at hgamma
      obtain ⟨c, hc, p, ps, hcform, hp, hgp⟩ :=
        E_omega_exists_coefficient hgamma
      exact ⟨c, by simp [omegaTerm.coefficients, hc], p, ps, hcform, hp, hgp⟩
  termination_by omegaTerm_cmplx a
  decreasing_by
    all_goals
      subst_vars
      simp [omegaTerm_cmplx] <;> omega

-- A principal component of a normal countable ordinal is at most the whole ordinal.
theorem principal_component_le_countable {p : _root_.principal}
        {ps : List _root_.principal} (hps : principalList_normal ps) (hp : p ∈ ps) :
        countableOrd.ofPrincipal p ≤c countableOrd.sum ps := by
  cases ps with
  | nil => simp at hp
  | cons q qs =>
    simp only [List.mem_cons] at hp
    have hpq : p ≤p q := by
      rcases hp with rfl | hp
      · exact Or.inr (principal_eq_refl p)
      · exact principalList_normal_tail_bounded hps p hp
    change countableOrd.sum [p] ≤c countableOrd.sum (q :: qs)
    rcases hpq with hpq | hpq
    · exact Or.inl (countableOrd_lt.sum (principalList_lt.head hpq))
    · cases qs with
      | nil =>
        exact Or.inr (countableOrd_eq.sum
          (principalList_eq.cons hpq principalList_eq.nil))
      | cons r rs =>
        exact Or.inl (countableOrd_lt.sum
          (principalList_lt.tail hpq principalList_lt.nil))
-- If a coefficient is below ψ(b), each principal component is below ψ(b).
theorem coefficient_component_lt_principal {p : _root_.principal}
        {ps : List _root_.principal} {b : _root_.omegaTerm}
        (hps : principalList_normal ps)
        (h : countableOrd.sum ps<ccountableOrd.ofPrincipal (.psi b))
        (hp : p ∈ ps) :
        p <p .psi b := by
  change countableOrd.sum ps <c countableOrd.sum [.psi b] at h
  cases h with
  | sum hlist =>
    cases ps with
    | nil => simp at hp
    | cons q qs =>
      cases hlist with
      | head hqb =>
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hqb
        · have hpq := principalList_normal_tail_bounded hps p hp
          rcases hpq with hpq | hpq
          · exact principal_lt_trans hpq hqb
          · exact principal_eq_lt_trans hpq hqb
      | tail _ htail => cases htail
-- If ψ(a) is at most a countable coefficient, some principal component dominates ψ(a).
theorem principal_le_countable_exists_component {a : _root_.omegaTerm}
        {c : _root_.countableOrd} (hc : countableOrd_normal c)
        (h : countableOrd.ofPrincipal (.psi a)≤cc) :
        ∃ p ps, c = .sum ps ∧ p ∈ ps ∧ (.psi a ≤p p) := by
  cases hc with
  | sum hps =>
    rename_i ps
    cases ps with
    | nil =>
      rcases h with h | h
      · cases h with | sum hlist => cases hlist
      · cases h with | sum hlist => cases hlist
    | cons p rest =>
      refine ⟨p, p :: rest, rfl, by simp, ?_⟩
      change countableOrd.sum [.psi a] ≤c countableOrd.sum (p :: rest) at h
      rcases h with h | h
      · cases h with
        | sum hlist =>
          cases hlist with
          | head hap => exact Or.inl hap
          | tail heq _ => exact Or.inr heq
      · cases h with
        | sum hlist =>
          cases hlist with
          | cons heq _ => exact Or.inr heq
end BHToFreund

namespace FreundTerm
mutual
theorem FreundTerm_tri (a b : FreundTerm) : a <f b ∨ a = b ∨ b <f a := by
  classical
  cases a with
  | Omega => cases b with
             | Omega => exact Or.inr (Or.inl rfl)
             | theta b => exact Or.inr (Or.inr FreundTerm_lt.theta_Omega)
             | cnf bs =>
              cases bs with
              | nil => exact Or.inr (Or.inr FreundTerm_lt.cnf_nil_Omega)
              | cons b bs =>
                rcases FreundTerm_tri (.Omega : FreundTerm) b with
                  hOb | heqOb | hbO
                · exact Or.inl (FreundTerm_lt.Omega_cnf_lt hOb)
                · subst b; exact Or.inl (FreundTerm_lt.Omega_cnf_eq)
                · exact Or.inr (Or.inr (FreundTerm_lt.cnf_Omega hbO))
  | theta a =>
      cases b with
      | Omega => exact Or.inl FreundTerm_lt.theta_Omega
      | theta b =>
          rcases FreundTerm_tri a b with hTab | hTeq | hTba
          · by_cases hE : ∀ g, g ∈ E a → g <f (.theta b : FreundTerm)
            · exact Or.inl (FreundTerm_lt.theta_theta_forward hTab hE)
            · push Not at hE
              obtain ⟨g, hg, hnot⟩ := hE
              have hgComplexity : complexity g < complexity (.theta a) :=
                E_mem_complexity_lt_theta hg
              rcases FreundTerm_tri g (.theta b) with hgb | heq | hbg
              · exact False.elim (hnot hgb)
              · subst g
                exact Or.inr (Or.inr (FreundTerm_lt.theta_theta_support_eq hg))
              · exact Or.inr
                  (Or.inr (FreundTerm_lt.theta_theta_support_lt hg hbg))
          · subst b
            exact Or.inr (Or.inl rfl)
          · by_cases hE : ∀ g, g ∈ E b → g <f (.theta a : FreundTerm)
            · exact Or.inr (Or.inr (FreundTerm_lt.theta_theta_forward hTba hE))
            · push Not at hE
              obtain ⟨g, hg, hnot⟩ := hE
              have hgComplexity : complexity g < complexity (.theta b) :=
                E_mem_complexity_lt_theta hg
              rcases FreundTerm_tri g (.theta a) with hga | heq | hag
              · exact False.elim (hnot hga)
              · subst g
                exact Or.inl (FreundTerm_lt.theta_theta_support_eq hg)
              · exact Or.inl (FreundTerm_lt.theta_theta_support_lt hg hag)
      | cnf bs =>
          cases bs with
          | nil => exact Or.inr (Or.inr FreundTerm_lt.cnf_nil_theta)
          | cons b bs =>
              rcases FreundTerm_tri (.theta a) b with hab | heq | hba
              · exact Or.inl (FreundTerm_lt.theta_cnf_lt hab)
              · subst b
                exact Or.inl FreundTerm_lt.theta_cnf_eq
              · exact Or.inr (Or.inr (FreundTerm_lt.cnf_theta hba))
  | cnf as =>
      cases b with
      | Omega =>
          cases as with
          | nil => exact Or.inl FreundTerm_lt.cnf_nil_Omega
          | cons a as =>
              rcases FreundTerm_tri a (.Omega : FreundTerm) with
                haO | heq | hOa
              · exact Or.inl (FreundTerm_lt.cnf_Omega haO)
              · subst a
                exact Or.inr (Or.inr FreundTerm_lt.Omega_cnf_eq)
              · exact Or.inr (Or.inr (FreundTerm_lt.Omega_cnf_lt hOa))
      | theta b =>
          cases as with
          | nil => exact Or.inl FreundTerm_lt.cnf_nil_theta
          | cons a as =>
              rcases FreundTerm_tri a (.theta b) with
                hab | heq | hba
              · exact Or.inl (FreundTerm_lt.cnf_theta hab)
              · subst a
                exact Or.inr (Or.inr FreundTerm_lt.theta_cnf_eq)
              · exact Or.inr (Or.inr (FreundTerm_lt.theta_cnf_lt hba))
      | cnf bs =>
          rcases FreundTermList_tri as bs with hab | heq | hba
          · exact Or.inl (FreundTerm_lt.cnf_cnf hab)
          · subst bs; exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (FreundTerm_lt.cnf_cnf hba))
termination_by
  complexity a + complexity b
decreasing_by
  all_goals
    subst_vars
    simp [complexity, complexityList] at *; omega
theorem FreundTermList_tri (as bs : List FreundTerm) : FreundTermList_lt as bs ∨
        as = bs ∨ FreundTermList_lt bs as := by
  cases as with
  | nil =>
      cases bs with
      | nil => exact Or.inr (Or.inl rfl)
      | cons b bs => exact Or.inl FreundTermList_lt.nil
  | cons a as =>
      cases bs with
      | nil => exact Or.inr (Or.inr FreundTermList_lt.nil)
      | cons b bs =>
          rcases FreundTerm_tri a b with hab | heq | hba
          · exact Or.inl (FreundTermList_lt.head hab)
          · subst b
            rcases FreundTermList_tri as bs with htail | heqTail | htailRev
            · exact Or.inl (FreundTermList_lt.tail htail)
            · subst bs; exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (FreundTermList_lt.tail htailRev))
          · exact Or.inr (Or.inr (FreundTermList_lt.head hba))
termination_by
  complexityList as + complexityList bs
decreasing_by
  all_goals
    subst_vars
    simp [complexityList] at *; omega
end

theorem FreundTerm_normal_tri (a b : NormalFreundTerm) :
    a.1 <f b.1 ∨ a.1 = b.1 ∨ b.1 <f a.1 := by
  exact FreundTerm_tri a.1 b.1

theorem cnfExponents_normal {a : FreundTerm} (ha : FreundTerm_normal a) :
        FreundTermList_normal (cnfExponents a) := by
  cases a with
  | Omega => simp only [cnfExponents]
             exact FreundTermList_normal.single FreundTerm_normal.Omega
  | theta a => cases ha with
               | theta ha =>
                 simp only [cnfExponents]
                 exact FreundTermList_normal.single (FreundTerm_normal.theta ha)
  | cnf as => cases ha with
              | cnf has hsingle => simpa only [cnfExponents] using has
theorem cnfExponents_lt {a b : FreundTerm} (ha : FreundTerm_normal a) (hb : FreundTerm_normal b)
        (hab : a <f b) : FreundTermList_lt (cnfExponents a) (cnfExponents b) := by
  have habCopy := hab
  cases hab with
  | Omega_cnf_lt hOb => simp only [cnfExponents]
                        exact FreundTermList_lt.head hOb
  | @Omega_cnf_eq bs =>
    simp only [cnfExponents]
    cases bs with
    | nil => cases hb with
             | cnf has hsingle =>
               have hbad : FreundSingletonOK (.Omega : FreundTerm) := hsingle .Omega rfl
               simp [FreundSingletonOK] at hbad
    | cons b bs => exact FreundTermList_lt.tail (FreundTermList_lt.nil)
  | theta_Omega => simp only [cnfExponents]
                   exact FreundTermList_lt.head FreundTerm_lt.theta_Omega
  | @theta_cnf_lt x y ys h => simp only [cnfExponents]
                              exact FreundTermList_lt.head h
  | @theta_cnf_eq x ys =>
    simp only [cnfExponents]
    cases ys with
    | nil => cases hb with
             | cnf has hsingle =>
               have hbad : FreundSingletonOK (.theta x : FreundTerm) :=
                hsingle (.theta x) rfl
               simp [FreundSingletonOK] at hbad
    | cons y ys => exact FreundTermList_lt.tail (FreundTermList_lt.nil)
  | theta_theta_forward harg hE =>
    simp only [cnfExponents]; exact FreundTermList_lt.head habCopy
  | theta_theta_support_lt hg hlt =>
      simp only [cnfExponents]; exact FreundTermList_lt.head habCopy
  | theta_theta_support_eq hg => simp only [cnfExponents]; exact FreundTermList_lt.head habCopy
  | cnf_nil_Omega => simp only [cnfExponents]; exact FreundTermList_lt.nil
  | cnf_nil_theta => simp only [cnfExponents]; exact FreundTermList_lt.nil
  | cnf_Omega h => simp only [cnfExponents]; exact FreundTermList_lt.head h
  | cnf_theta h => simp only [cnfExponents]; exact FreundTermList_lt.head h
  | cnf_cnf h => simpa only [cnfExponents] using h
@[simp]
theorem keepGE_nil (b : FreundTerm) : keepGE b [] = [] := by rfl
theorem keepGE_cons_of_le {a b : FreundTerm} {as : List FreundTerm} (h : b ≤f a) :
        keepGE b (a :: as) = a :: keepGE b as := by
  classical
  simp [keepGE, h]
theorem keepGE_cons_of_not_le {a b : FreundTerm} {as : List FreundTerm} (h : ¬ b ≤f a) :
        keepGE b (a :: as) = [] := by
  classical
  simp [keepGE, h]
theorem mem_keepGE {cutoff t : FreundTerm} {as : List FreundTerm} (ht : t ∈ keepGE cutoff as) :
        t ∈ as := by
  classical
  induction as with
  | nil => simp [keepGE] at ht
  | cons a as ih =>
      by_cases h : cutoff ≤f a
      · rw [keepGE_cons_of_le h] at ht
        simp only [List.mem_cons] at ht ⊢
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (ih ht)
      · rw [keepGE_cons_of_not_le h] at ht; simp at ht
theorem keepGE_normal {cutoff : FreundTerm} {as : List FreundTerm}
        (has : FreundTermList_normal as) :
        FreundTermList_normal (keepGE cutoff as) := by
  classical
  cases as with
  | nil => rw [keepGE_nil]; exact FreundTermList_normal.nil
  | cons a as =>
      by_cases ha : cutoff ≤f a
      · rw [keepGE_cons_of_le ha]
        cases as with
        | nil =>
            rw [keepGE_nil]
            exact FreundTermList_normal.single (FreundTermList_normal_head has)
        | cons b bs =>
            by_cases hb : cutoff ≤f b
            · rw [keepGE_cons_of_le hb]
              apply FreundTermList_normal.cons
              · exact FreundTerm.FreundTermList_normal_head has
              · have htail : FreundTermList_normal (b :: bs) :=
                  FreundTermList_normal_tail has
                have hkeep : FreundTermList_normal (keepGE cutoff (b :: bs)) :=
                  keepGE_normal htail
                rw [keepGE_cons_of_le hb] at hkeep; exact hkeep
              · intro t ht
                apply FreundTermList_normal_tail_bounded has t
                simp only [List.mem_cons] at ht ⊢
                rcases ht with rfl | ht
                · exact Or.inl rfl
                · exact Or.inr (mem_keepGE ht)
            · rw [keepGE_cons_of_not_le hb]
              exact FreundTermList_normal.single (FreundTermList_normal_head has)
      · rw [keepGE_cons_of_not_le ha]; exact FreundTermList_normal.nil
theorem FreundTermList_normal_cons_of_nonempty {a : FreundTerm} {bs : List FreundTerm}
        (ha : FreundTerm_normal a) (hbs : FreundTermList_normal bs) (hne : bs ≠ [])
        (hbound : ∀ t, t ∈ bs → t ≤f a) : FreundTermList_normal (a :: bs) := by
  cases bs with
  | nil => exact False.elim (hne rfl)
  | cons b bs =>
      exact FreundTermList_normal.cons ha hbs hbound
theorem keepGE_append_normal {cutoff : FreundTerm} {as cs : List FreundTerm}
        (has : FreundTermList_normal as) (hcs : FreundTermList_normal (cutoff :: cs)) :
        FreundTermList_normal (keepGE cutoff as ++ (cutoff :: cs)) := by
  classical
  cases as with
  | nil => simp only [keepGE_nil, List.nil_append]; exact hcs
  | cons a as =>
      by_cases hca : cutoff ≤f a
      · rw [keepGE_cons_of_le hca]; simp only [List.cons_append]
        apply FreundTermList_normal_cons_of_nonempty
        · exact FreundTermList_normal_head has
        · exact keepGE_append_normal (FreundTermList_normal_tail has) hcs
        · simp
        · intro t ht
          rw [List.mem_append] at ht
          rcases ht with ht | ht
          · apply FreundTermList_normal_tail_bounded has t
            exact mem_keepGE ht
          · simp only [List.mem_cons] at ht
            rcases ht with rfl | ht
            · exact hca
            · exact FreundTerm_le_trans (FreundTermList_normal_tail_bounded hcs t ht) hca
      · rw [keepGE_cons_of_not_le hca]; simp only [List.nil_append]; exact hcs
theorem cnfAdd_normal {a b : FreundTerm} (ha : FreundTerm_normal a) (hb : FreundTerm_normal b) :
        FreundTerm_normal (cnfAdd a b) := by
  classical
  cases hExp : cnfExponents b with
  | nil => simp only [cnfAdd, hExp]; exact ha
  | cons c cs =>
      have haExp : FreundTermList_normal (cnfExponents a) :=
        cnfExponents_normal ha
      have hbExp : FreundTermList_normal (c :: cs) := by
        have h := cnfExponents_normal hb; rw [hExp] at h; exact h
      have hnormal : FreundTermList_normal (keepGE c (cnfExponents a) ++ (c :: cs)) :=
        keepGE_append_normal haExp hbExp
      simp only [cnfAdd, hExp]; exact packCNF_normal hnormal
theorem FreundTermList_lt_append_left {as bs : List FreundTerm} (prefixx : List FreundTerm)
        (h : FreundTermList_lt as bs) :
        FreundTermList_lt (prefixx ++ as) (prefixx ++ bs) := by
  induction prefixx with
  | nil => simpa using h
  | cons a prefixx ih =>
      simp only [List.cons_append]; exact FreundTermList_lt.tail ih
theorem FreundTermList_lt_keepGE_append {cutoff : FreundTerm} {as cs : List FreundTerm}
        (hcutoff : FreundTerm_normal cutoff) (has : FreundTermList_normal as) :
        FreundTermList_lt as (keepGE cutoff as ++ (cutoff :: cs)) := by
  classical
  cases as with
  | nil => simp only [keepGE, List.nil_append]
           exact FreundTermList_lt.nil
  | cons a as =>
      by_cases hca : cutoff ≤f a
      · rw [keepGE_cons_of_le hca]; simp only [List.cons_append]
        exact FreundTermList_lt.tail
          (FreundTermList_lt_keepGE_append hcutoff (FreundTermList_normal_tail has))
      · rw [keepGE_cons_of_not_le hca]; simp only [List.nil_append]
        have ha : FreundTerm_normal a := FreundTermList_normal_head has
        rcases FreundTerm_normal_tri ⟨cutoff, hcutoff⟩ ⟨a, ha⟩ with hlt | heq | hgt
        · exact False.elim (hca (Or.inl hlt))
        · exact False.elim (hca (Or.inr heq))
        · exact FreundTermList_lt.head hgt
theorem keepGE_append_lt_of_lt {a b : FreundTerm} {base as bs : List FreundTerm}
        (hbase : FreundTermList_normal base) (ha : FreundTerm_normal a) (hb : FreundTerm_normal b)
        (hab : a <f b) :
        FreundTermList_lt (keepGE a base ++ (a :: as)) (keepGE b base ++ (b :: bs)) := by
  classical
  cases base with
  | nil => simp only [keepGE, List.nil_append]; exact FreundTermList_lt.head hab
  | cons d ds =>
      have hd : FreundTerm_normal d := FreundTermList_normal_head hbase
      have hds : FreundTermList_normal ds := FreundTermList_normal_tail hbase
      by_cases hbd : b ≤f d
      · have had : a ≤f d := FreundTerm_le_trans (Or.inl hab) hbd
        rw [keepGE_cons_of_le hbd]
        rw [keepGE_cons_of_le had]
        simp only [List.cons_append]
        exact FreundTermList_lt.tail (keepGE_append_lt_of_lt hds ha hb hab)
      · have hdb : d <f b := by
          rcases FreundTerm_normal_tri ⟨b, hb⟩ ⟨d, hd⟩ with hbd' | heq | hdb
          · exact False.elim (hbd (Or.inl hbd'))
          · exact False.elim (hbd (Or.inr heq))
          · exact hdb
        by_cases had : a ≤f d
        · rw [keepGE_cons_of_le had]
          rw [keepGE_cons_of_not_le hbd]
          simp only [List.cons_append, List.nil_append]
          exact FreundTermList_lt.head hdb
        · rw [keepGE_cons_of_not_le had]
          rw [keepGE_cons_of_not_le hbd]
          simp only [List.nil_append]
          exact FreundTermList_lt.head hab
theorem packCNF_lt_of_normal_list_lt {as bs : List FreundTerm} (has : FreundTermList_normal as)
        (hbs : FreundTermList_normal bs) (hab : FreundTermList_lt as bs) :
        packCNF as <f packCNF bs := by
  have ha : FreundTerm_normal (packCNF as) := packCNF_normal has
  have hb : FreundTerm_normal (packCNF bs) := packCNF_normal hbs
  rcases FreundTerm_normal_tri ⟨packCNF as, ha⟩ ⟨packCNF bs, hb⟩ with hlt | heq | hgt
  · exact hlt
  · have hLists : as = bs := by
      have h := congrArg cnfExponents heq
      simpa using h
    subst bs
    exact False.elim (FreundTermList_lt_irrefl as hab)
  · have hreverse : FreundTermList_lt bs as := by
      have h := cnfExponents_lt hb ha hgt
      simpa using h
    have hself : FreundTermList_lt as as := FreundTermList_lt_trans hab hreverse
    exact False.elim
      (FreundTermList_lt_irrefl as hself)

-- Freund addition is strictly monotone in the right argument
-- on normal Freund terms.
theorem cnfAdd_right_lt {base a b : FreundTerm} (hbase : FreundTerm_normal base)
        (ha : FreundTerm_normal a) (hb : FreundTerm_normal b) (hab : a <f b) :
        cnfAdd base a <f cnfAdd base b := by
  classical
  have hbaseExp : FreundTermList_normal (cnfExponents base) := cnfExponents_normal hbase
  have haExp : FreundTermList_normal (cnfExponents a) :=
    cnfExponents_normal ha
  have hbExp : FreundTermList_normal (cnfExponents b) :=
    cnfExponents_normal hb
  have habExp : FreundTermList_lt (cnfExponents a) (cnfExponents b) :=
    cnfExponents_lt ha hb hab
  cases haE : cnfExponents a with
  | nil =>
      cases hbE : cnfExponents b with
      | nil =>
          rw [haE, hbE] at habExp
          exact False.elim (FreundTermList_lt_irrefl [] habExp)
      | cons c cs =>
          have hbList : FreundTermList_normal (c :: cs) := by
            rw [hbE] at hbExp; exact hbExp
          have hc : FreundTerm_normal c := FreundTermList_normal_head hbList
          have hout : FreundTermList_normal (keepGE c (cnfExponents base) ++
                      (c :: cs)) :=
            keepGE_append_normal hbaseExp hbList
          have hlist : FreundTermList_lt (cnfExponents base)
                       (keepGE c (cnfExponents base) ++ (c :: cs)) :=
            FreundTermList_lt_keepGE_append hc hbaseExp
          have hpack : packCNF (cnfExponents base) <f
                       packCNF (keepGE c (cnfExponents base) ++ (c :: cs)) :=
            packCNF_lt_of_normal_list_lt hbaseExp hout hlist
          rw [packCNF_cnfExponents_of_normal hbase] at hpack
          simpa [cnfAdd, haE, hbE] using hpack
  | cons a₀ as =>
      cases hbE : cnfExponents b with
      | nil => rw [haE, hbE] at habExp; cases habExp
      | cons b₀ bs =>
          have haList : FreundTermList_normal (a₀ :: as) := by
            rw [haE] at haExp; exact haExp
          have hbList : FreundTermList_normal (b₀ :: bs) := by
            rw [hbE] at hbExp; exact hbExp
          have houtA : FreundTermList_normal (keepGE a₀ (cnfExponents base) ++
                       (a₀ :: as)) :=
            keepGE_append_normal hbaseExp haList
          have houtB : FreundTermList_normal (keepGE b₀ (cnfExponents base) ++
                       (b₀ :: bs)) :=
            keepGE_append_normal hbaseExp hbList
          rw [haE, hbE] at habExp
          have hlist : FreundTermList_lt (keepGE a₀ (cnfExponents base) ++
                       (a₀ :: as)) (keepGE b₀ (cnfExponents base) ++
                       (b₀ :: bs)) := by
            cases habExp with
            | head hhead =>
                exact keepGE_append_lt_of_lt hbaseExp (FreundTermList_normal_head haList)
                      (FreundTermList_normal_head hbList) hhead
            | tail htail =>
                exact FreundTermList_lt_append_left (keepGE a₀ (cnfExponents base))
                      (FreundTermList_lt.tail htail)
          have hpack : packCNF (keepGE a₀ (cnfExponents base) ++
                       (a₀ :: as)) <f packCNF (keepGE b₀ (cnfExponents base) ++
                       (b₀ :: bs)) :=
            packCNF_lt_of_normal_list_lt houtA houtB hlist
          simpa [cnfAdd, haE, hbE] using hpack
theorem cnfAdd_map_normal {base : FreundTerm} {as : List FreundTerm}
        (hbase : FreundTerm_normal base) (has : FreundTermList_normal as) :
        FreundTermList_normal (as.map (fun a => cnfAdd base a)) := by
  cases as with
  | nil => exact FreundTermList_normal.nil
  | cons a as =>
      cases as with
      | nil =>
          cases has with
          | single ha => simp only [List.map_cons, List.map_nil]
                         exact FreundTermList_normal.single (cnfAdd_normal hbase ha)
      | cons b bs =>
          cases has with
          | cons ha htail hbound =>
              simp only [List.map_cons]
              apply FreundTermList_normal.cons
              · exact cnfAdd_normal hbase ha
              · exact cnfAdd_map_normal hbase htail
              · intro t ht
                have htMap : t ∈ (b :: bs).map (fun s => cnfAdd base s) := by
                  simpa only [List.map_cons] using ht
                obtain ⟨s, hs, hst⟩ := List.mem_map.mp htMap
                subst t
                have hsNormal : FreundTerm_normal s := FreundTermList_normal_mem htail s hs
                have hsa : s ≤f a := hbound s hs
                rcases hsa with hlt | heq
                · exact Or.inl (cnfAdd_right_lt hbase hsNormal ha hlt)
                · subst s; exact Or.inr rfl

theorem cnfAdd_map_lt {base : FreundTerm} {as bs : List FreundTerm} (hbase : FreundTerm_normal base)
        (has : FreundTermList_normal as) (hbs : FreundTermList_normal bs)
        (hab : FreundTermList_lt as bs) :
        FreundTermList_lt (as.map (fun a => cnfAdd base a)) (bs.map (fun b => cnfAdd base b)) := by
  cases hab with
  | nil => simp only [List.map_nil, List.map_cons]
           exact FreundTermList_lt.nil
  | head hhead =>
    simp only [List.map_cons]
    exact FreundTermList_lt.head (cnfAdd_right_lt hbase (FreundTermList_normal_head has)
          (FreundTermList_normal_head hbs) hhead)
  | tail htail =>
    simp only [List.map_cons]
    exact FreundTermList_lt.tail
        (cnfAdd_map_lt hbase (FreundTermList_normal_tail has) (FreundTermList_normal_tail hbs)
          htail)


theorem OmegaMul_lt {a b : FreundTerm} (ha : FreundTerm_normal a) (hb : FreundTerm_normal b)
        (hab : a <f b) : OmegaMul a <f OmegaMul b := by
  have haExp : FreundTermList_normal (cnfExponents a) := cnfExponents_normal ha
  have hbExp : FreundTermList_normal (cnfExponents b) := cnfExponents_normal hb
  have habExp : FreundTermList_lt (cnfExponents a) (cnfExponents b) :=
    cnfExponents_lt ha hb hab
  have hOmega : FreundTerm_normal (.Omega : FreundTerm) := FreundTerm_normal.Omega
  have haMap : FreundTermList_normal ((cnfExponents a).map (fun e => cnfAdd .Omega e)) :=
    cnfAdd_map_normal hOmega haExp
  have hbMap : FreundTermList_normal ((cnfExponents b).map (fun e => cnfAdd .Omega e)) :=
    cnfAdd_map_normal hOmega hbExp
  have habMap : FreundTermList_lt ((cnfExponents a).map (fun e => cnfAdd .Omega e))
                ((cnfExponents b).map (fun e => cnfAdd .Omega e)) :=
    cnfAdd_map_lt hOmega haExp hbExp habExp
  exact packCNF_lt_of_normal_list_lt haMap hbMap habMap
-- Shifting a normal exponent list preserves Freund list normality.
theorem shiftExponents_normal {base beta : FreundTerm} (hbase : FreundTerm_normal base)
        (hbeta : FreundTerm_normal beta) :
        FreundTermList_normal (shiftExponents base beta) := by
  unfold shiftExponents
  exact cnfAdd_map_normal hbase (cnfExponents_normal hbeta)
theorem OmegaMul_normal {a : FreundTerm} (ha : FreundTerm_normal a) :
        FreundTerm_normal (OmegaMul a) := by
  unfold OmegaMul; apply packCNF_normal
  exact cnfAdd_map_normal FreundTerm_normal.Omega (cnfExponents_normal ha)
theorem shiftExponents_lt {base a b : FreundTerm} (hbase : FreundTerm_normal base)
        (ha : FreundTerm_normal a) (hb : FreundTerm_normal b) (hab : a <f b) :
        FreundTermList_lt (shiftExponents base a) (shiftExponents base b) := by
  unfold shiftExponents
  apply cnfAdd_map_lt hbase (cnfExponents_normal ha) (cnfExponents_normal hb)
  exact cnfExponents_lt ha hb hab
theorem cnf_nil_lt_packCNF_of_nonempty {as : List FreundTerm} (hne : as ≠ []) :
        (.cnf [] : FreundTerm) <f packCNF as := by
  cases as with
  | nil => exact False.elim (hne rfl)
  | cons a as =>
    cases as with
    | nil =>
      cases a with
      | Omega => exact FreundTerm_lt.cnf_nil_Omega
      | theta b => exact FreundTerm_lt.cnf_nil_theta
      | cnf bs =>
        simp only [packCNF]; exact FreundTerm_lt.cnf_cnf FreundTermList_lt.nil
    | cons b bs =>
          simp only [packCNF]; exact FreundTerm_lt.cnf_cnf FreundTermList_lt.nil
theorem keepGE_eq_self_of_forall {cutoff : FreundTerm} {as : List FreundTerm}
        (h : ∀ t, t ∈ as → cutoff ≤f t) : keepGE cutoff as = as := by
  classical
  cases as with
  | nil => rfl
  | cons a as =>
    have ha : cutoff ≤f a := h a (by simp)
    rw [keepGE_cons_of_le ha]
    have htail : keepGE cutoff as = as := by
      apply keepGE_eq_self_of_forall
      intro t ht
      exact h t (by simp [ht])
    rw [htail]
theorem Omega_le_cnfAdd_Omega (a : FreundTerm) : (.Omega : FreundTerm) ≤f cnfAdd .Omega a := by
  classical
  cases hExp : cnfExponents a with
  | nil => rw [cnfAdd, hExp]; simp only []; exact Or.inr rfl
  | cons c cs =>
    by_cases hc : c ≤f (.Omega : FreundTerm)
    · have hEq : cnfAdd (.Omega : FreundTerm) a =
           .cnf ((.Omega : FreundTerm) :: c :: cs) := by
          rw [cnfAdd, hExp]; simp only [cnfExponents]
          rw [keepGE_cons_of_le hc]; simp [keepGE, packCNF]
      rw [hEq]
      exact Or.inl FreundTerm_lt.Omega_cnf_eq
    · rcases FreundTerm_tri c (.Omega : FreundTerm) with hcO | heq | hOc
      · exact False.elim (hc (Or.inl hcO))
      · exact False.elim (hc (Or.inr heq))
      · cases cs with
        | nil =>
          cases c with
          | Omega => exact False.elim ((FreundTerm_lt_irrefl (.Omega : FreundTerm)) hOc)
          | theta d => cases hOc
          | cnf ds =>
            have hEq : cnfAdd (.Omega : FreundTerm) a = .cnf [(.cnf ds : FreundTerm)] := by
              rw [cnfAdd, hExp]
              simp only [cnfExponents]
              rw [keepGE_cons_of_not_le hc]
              simp [packCNF]
            rw [hEq]
            exact Or.inl (FreundTerm_lt_trans hOc
                         (FreundTerm_lt_cnf_cons_self (.cnf ds : FreundTerm) []))
        | cons d ds =>
            have hEq : cnfAdd (.Omega : FreundTerm) a = .cnf (c :: d :: ds) := by
              rw [cnfAdd, hExp]
              simp only [cnfExponents]
              rw [keepGE_cons_of_not_le hc]
              simp [packCNF]
            rw [hEq]
            exact Or.inl (FreundTerm_lt.Omega_cnf_lt hOc)
theorem Omega_le_of_mem_cnfExponents_OmegaMul {a t : FreundTerm}
        (ht : t ∈ cnfExponents (OmegaMul a)) :
        (.Omega : FreundTerm) ≤f t := by
  have htMap : t ∈ (cnfExponents a).map (fun e => cnfAdd .Omega e) := by
    simpa [OmegaMul] using ht
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp htMap
  exact Omega_le_cnfAdd_Omega e
theorem FreundTermList_lt_append_small {as bs : List FreundTerm} {x y : FreundTerm}
        (hab : FreundTermList_lt as bs) (hbs : ∀ t, t ∈ bs → (.Omega : FreundTerm) ≤f t)
        (hx : x <f (.Omega : FreundTerm)) :
        FreundTermList_lt (as ++ [x]) (bs ++ [y]) := by
  cases hab with
  | @nil b bs =>
      simp only [List.nil_append, List.cons_append]
      apply FreundTermList_lt.head
      exact FreundTerm_lt_of_lt_of_le hx (hbs b (by simp))
  | @head a b as bs hab =>
      simp only [List.cons_append]
      exact FreundTermList_lt.head hab
  | @tail a as bs htail =>
      simp only [List.cons_append]
      apply FreundTermList_lt.tail
      apply FreundTermList_lt_append_small htail
      · intro t ht
        exact hbs t (by simp [ht])
      · exact hx
theorem FreundTermList_mem_lt_singleton {as : List FreundTerm} {b x : FreundTerm}
        (has : FreundTermList_normal as) (hab : FreundTermList_lt as [b])
        (hx : x ∈ as) : x <f b := by
  cases as with
  | nil => simp at hx
  | cons a as =>
    cases hab with
    | head hab =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hab
      · have hxa : x ≤f a := FreundTermList_normal_tail_bounded has x hx
        exact FreundTerm_lt_of_le_of_lt hxa hab
    | tail htail => cases htail
theorem FreundTermList_lt_append_below {as bs xs ys : List FreundTerm} {cutoff : FreundTerm}
        (hab : FreundTermList_lt as bs) (hbs : ∀ t, t ∈ bs → cutoff ≤f t)
        (hxs : ∀ t, t ∈ xs → t <f cutoff) :
        FreundTermList_lt (as ++ xs) (bs ++ ys) := by
  induction as generalizing bs xs ys with
  | nil =>
    cases bs with
    | nil => cases hab
    | cons b bs =>
      cases xs with
      | nil => simp only [List.nil_append, List.cons_append]
               exact FreundTermList_lt.nil
      | cons x xs =>
        simp only [List.nil_append, List.cons_append]
        apply FreundTermList_lt.head
        exact FreundTerm_lt_of_lt_of_le (hxs x (by simp)) (hbs b (by simp))
  | cons a as ih =>
      cases bs with
      | nil => cases hab
      | cons b bs =>
          cases hab with
          | head hab => simp only [List.cons_append]
                        exact FreundTermList_lt.head hab
          | tail htail =>
              simp only [List.cons_append]; apply FreundTermList_lt.tail
              apply ih htail
              · intro t ht; exact hbs t (by simp [ht])
              · exact hxs

end FreundTerm

namespace BHToFreund
theorem countable_zero_lt_nonempty {beta : _root_.countableOrd} (hbeta : countableOrd.zero<cbeta) :
        ∃ p ps, beta = .sum (p :: ps) := by
  cases beta with
  | sum ps =>
    cases ps with
    | nil =>
      change countableOrd.sum [] <c countableOrd.sum [] at hbeta
      exact False.elim (countableOrd_lt_irrefl hbeta)
    | cons p ps => exact ⟨p, ps, rfl⟩
theorem shiftExponents_countable_nonempty {base : FreundTerm} {beta : _root_.countableOrd}
        (hbeta : countableOrd.zero<cbeta) :
        FreundTerm.shiftExponents base (countable beta) ≠ [] := by
  obtain ⟨p, ps, rfl⟩ := countable_zero_lt_nonempty hbeta
  simp [FreundTerm.shiftExponents, principalList]
theorem omega_zero_lt_omegaNF_map {alpha gamma : _root_.omegaTerm} {beta : _root_.countableOrd}
        (hbeta : countableOrd.zero<cbeta) :
        omega .zero <f omega (.omegaNF alpha beta gamma) := by
  rw [omega_zero, omega_omegaNF]
  apply FreundTerm.cnf_nil_lt_packCNF_of_nonempty
  have hshift : FreundTerm.shiftExponents (FreundTerm.OmegaMul (omega alpha))
                (countable beta) ≠ [] :=
    shiftExponents_countable_nonempty hbeta
  intro hnil
  have hparts : FreundTerm.shiftExponents (FreundTerm.OmegaMul (omega alpha))
                (countable beta) = [] ∧ FreundTerm.cnfExponents (omega gamma) = [] := by
    simpa using hnil
  exact hshift hparts.1
theorem principal_lt_Omega (p : _root_.principal) : principal p <f (.Omega : FreundTerm) := by
  cases p with
  | psi a => exact FreundTerm_lt.theta_Omega
theorem keepGE_principal_OmegaMul {a : FreundTerm} (p : _root_.principal) :
        FreundTerm.keepGE (principal p) (FreundTerm.cnfExponents (FreundTerm.OmegaMul a)) =
        FreundTerm.cnfExponents (FreundTerm.OmegaMul a) := by
  apply FreundTerm.keepGE_eq_self_of_forall; intro t ht
  have hpO : principal p <f (.Omega : FreundTerm) := principal_lt_Omega p
  have hOt : (.Omega : FreundTerm) ≤f t :=
              FreundTerm.Omega_le_of_mem_cnfExponents_OmegaMul ht
  exact Or.inl (FreundTerm.FreundTerm_lt_of_lt_of_le hpO hOt)
theorem cnfAdd_OmegaMul_principal (a : FreundTerm) (p : _root_.principal) :
        FreundTerm.cnfAdd (FreundTerm.OmegaMul a) (principal p) =
        FreundTerm.packCNF (FreundTerm.cnfExponents (FreundTerm.OmegaMul a) ++ [principal p]) := by
  classical
  cases p with
  | psi b =>
      have hkeep :
          FreundTerm.keepGE (principal (.psi b)) (FreundTerm.cnfExponents (FreundTerm.OmegaMul a)) =
            FreundTerm.cnfExponents (FreundTerm.OmegaMul a) :=
        keepGE_principal_OmegaMul (a := a) (p := .psi b)
      simpa [principal, FreundTerm.cnfAdd, FreundTerm.cnfExponents] using
        congrArg (fun xs => FreundTerm.packCNF (xs ++ [principal (.psi b)])) hkeep
-- Every principal component of a source coefficient occurs in E of the translated omega term.
-- Every principal component of a source coefficient occurs in E of the translated omega term.
theorem coefficient_principal_mem_E_omega {a : _root_.omegaTerm} {c : _root_.countableOrd}
        {p : _root_.principal} {ps : List _root_.principal} (ha : omegaTerm_normal a)
        (hc : c ∈ omegaTerm.coefficients a) (hcform : c = .sum ps) (hp : p ∈ ps) :
        principal p ∈ FreundTerm.E (omega a) := by
  have EList_mem_of_mem :
      ∀ {xs : List FreundTerm} {x g : FreundTerm}, x ∈ xs →
        g ∈ FreundTerm.E x → g ∈ FreundTerm.EList xs := by
    intro xs
    induction xs with
    | nil => intro x g hx hg; simp at hx
    | cons y ys ih =>
        intro x g hx hg; simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp only [FreundTerm.EList, List.mem_append]; exact Or.inl hg
        · simp only [FreundTerm.EList, List.mem_append]
          exact Or.inr (ih hx hg)
  cases a with
  | zero =>
      simp only [omegaTerm.coefficients, List.mem_singleton] at hc
      rw [hc] at hcform
      change countableOrd.sum [] = countableOrd.sum ps at hcform
      injection hcform with hps; subst ps; simp at hp
  | omegaNF alpha beta gamma =>
      cases ha with
      | omegaNF hAlpha hBeta hGamma hpos hrem =>
          simp only [omegaTerm.coefficients, List.mem_append, List.mem_singleton] at hc
          rcases hc with (hcAlpha | hcGamma) | hcBeta
          · have hAlphaMem : principal p ∈ FreundTerm.E (omega alpha) :=
              coefficient_principal_mem_E_omega hAlpha hcAlpha hcform hp
            have hBetaNonempty : ∃ q qs, beta = .sum (q :: qs) := by
              cases beta with
              | sum bs =>
                cases bs with
              | nil => change countableOrd.sum [] <c countableOrd.sum [] at hpos
                       exact False.elim (countableOrd_lt_irrefl hpos)
              | cons q qs => exact ⟨q, qs, rfl⟩
            obtain ⟨q, qs, hBetaForm⟩ :=  hBetaNonempty; subst beta
            have hqExp : principal q ∈ FreundTerm.cnfExponents (countable (.sum (q :: qs))) :=
              principal_mem_countable_exponents (by simp)
            have hqShift : FreundTerm.cnfAdd (FreundTerm.OmegaMul (omega alpha)) (principal q)
                           ∈
                           FreundTerm.shiftExponents (FreundTerm.OmegaMul (omega alpha))
                            (countable (.sum (q :: qs))) := by
              unfold FreundTerm.shiftExponents
              exact List.mem_map.mpr ⟨principal q, hqExp, rfl⟩
            have hBaseMem : principal p ∈ FreundTerm.E (FreundTerm.OmegaMul (omega alpha)) := by
              rw [FreundTerm.E_OmegaMul]; exact hAlphaMem
            have hAddMem : principal p ∈ FreundTerm.E (FreundTerm.cnfAdd (FreundTerm.OmegaMul
                           (omega alpha)) (principal q)) := by
              rw [cnfAdd_OmegaMul_principal, FreundTerm.E_packCNF, FreundTerm.EList_append]
              apply List.mem_append.mpr; left; rw [FreundTerm.EList_cnfExponents]
              exact hBaseMem
            have hShiftMem : principal p ∈ FreundTerm.EList (FreundTerm.shiftExponents
                             (FreundTerm.OmegaMul (omega alpha)) (countable (.sum (q :: qs)))) :=
              EList_mem_of_mem hqShift hAddMem
            rw [omega_omegaNF, FreundTerm.E_packCNF, FreundTerm.EList_append]
            apply List.mem_append.mpr; exact Or.inl hShiftMem
          · have hGammaMem : principal p ∈ FreundTerm.E (omega gamma) :=
              coefficient_principal_mem_E_omega hGamma hcGamma hcform hp
            rw [omega_omegaNF, FreundTerm.E_packCNF, FreundTerm.EList_append]
            apply List.mem_append.mpr; right; rw [FreundTerm.EList_cnfExponents]
            exact hGammaMem
          · subst c; subst beta
            have hpExp : principal p ∈ FreundTerm.cnfExponents (countable (.sum ps)) :=
              principal_mem_countable_exponents hp
            have hpShift : FreundTerm.cnfAdd (FreundTerm.OmegaMul (omega alpha)) (principal p)
                  ∈ FreundTerm.shiftExponents (FreundTerm.OmegaMul (omega alpha))
                    (countable (.sum ps)) := by
              unfold FreundTerm.shiftExponents
              exact List.mem_map.mpr ⟨principal p, hpExp, rfl⟩
            have hpSelf : principal p ∈ FreundTerm.E (principal p) := by
              cases p with
              | psi d => simp [principal, FreundTerm.E]
            have hAddMem : principal p ∈ FreundTerm.E
                           (FreundTerm.cnfAdd (FreundTerm.OmegaMul (omega alpha)) (principal p)) :=
              FreundTerm.E_right_mem_cnfAdd hpSelf
            have hShiftMem : principal p ∈ FreundTerm.EList (FreundTerm.shiftExponents
                             (FreundTerm.OmegaMul (omega alpha)) (countable (.sum ps))) :=
              EList_mem_of_mem hpShift hAddMem
            rw [omega_omegaNF, FreundTerm.E_packCNF, FreundTerm.EList_append]
            apply List.mem_append.mpr; exact Or.inl hShiftMem

theorem principal_one_map_normal : FreundTerm_normal (principal (_root_.principal.one)) := by
  change FreundTerm_normal (.theta (omega (.zero : _root_.omegaTerm)))
  apply FreundTerm_normal.theta; rw [omega_zero]; apply FreundTerm_normal.cnf
  · exact FreundTermList_normal.nil
  · intro a h; simp at h
theorem principal_one_le_map {p : _root_.principal} (hp : principal_normal p) :
        principal (_root_.principal.one) ≤f principal p := by
  cases p with
  | psi a =>
      cases hp with
      | psi ha hcoeff =>
          cases a with
          | zero =>
              exact Or.inr rfl
          | omegaNF alpha beta gamma =>
              cases ha with
              | omegaNF hAlpha hBeta hGamma hpos hrem =>
                  apply Or.inl
                  change (.theta (omega (.zero : _root_.omegaTerm)) : FreundTerm)
                         <f .theta (omega (.omegaNF alpha beta gamma))
                  apply FreundTerm_lt.theta_theta_forward
                  · exact omega_zero_lt_omegaNF_map hpos
                  · intro g hg
                    simp [omega_zero, FreundTerm.E, FreundTerm.EList] at hg
theorem cnfAdd_OmegaMul_principal_lt {a b : FreundTerm} (ha : FreundTerm_normal a)
        (hb : FreundTerm_normal b) (hab : a <f b) (p q : _root_.principal)
        (hp : FreundTerm_normal (principal p)) (hq : FreundTerm_normal (principal q)) :
        FreundTerm.cnfAdd (FreundTerm.OmegaMul a) (principal p)
        <f FreundTerm.cnfAdd (FreundTerm.OmegaMul b) (principal q) := by
  have hBaseA : FreundTerm_normal (FreundTerm.OmegaMul a) := FreundTerm.OmegaMul_normal ha
  have hBaseB : FreundTerm_normal (FreundTerm.OmegaMul b) := FreundTerm.OmegaMul_normal hb
  have hBaseLt : FreundTerm.OmegaMul a <f FreundTerm.OmegaMul b := FreundTerm.OmegaMul_lt ha hb hab
  have hExpLt : FreundTermList_lt (FreundTerm.cnfExponents (FreundTerm.OmegaMul a))
                (FreundTerm.cnfExponents (FreundTerm.OmegaMul b)) :=
    FreundTerm.cnfExponents_lt hBaseA hBaseB hBaseLt
  have hTargetGE : ∀ t, t ∈ FreundTerm.cnfExponents (FreundTerm.OmegaMul b) →
        (.Omega : FreundTerm) ≤f t := by
    intro t ht
    exact FreundTerm.Omega_le_of_mem_cnfExponents_OmegaMul ht
  have hpOmega : principal p <f (.Omega : FreundTerm) := principal_lt_Omega p
  have hListLt : FreundTermList_lt (FreundTerm.cnfExponents (FreundTerm.OmegaMul a) ++
                 [principal p])
                 (FreundTerm.cnfExponents (FreundTerm.OmegaMul b) ++ [principal q]) := by
    exact FreundTerm.FreundTermList_lt_append_small hExpLt hTargetGE hpOmega
  have hListA : FreundTermList_normal (FreundTerm.cnfExponents (FreundTerm.OmegaMul a) ++
                [principal p]) := by
    have hNormal : FreundTerm_normal (FreundTerm.cnfAdd (FreundTerm.OmegaMul a)
                   (principal p)) :=
      FreundTerm.cnfAdd_normal hBaseA hp
    have hExpNormal := FreundTerm.cnfExponents_normal hNormal
    rw [cnfAdd_OmegaMul_principal, FreundTerm.cnfExponents_packCNF] at hExpNormal
    exact hExpNormal
  have hListB : FreundTermList_normal (FreundTerm.cnfExponents (FreundTerm.OmegaMul b) ++
                [principal q]) := by
    have hNormal : FreundTerm_normal (FreundTerm.cnfAdd (FreundTerm.OmegaMul b)
                   (principal q)) :=
      FreundTerm.cnfAdd_normal hBaseB hq
    have hExpNormal := FreundTerm.cnfExponents_normal hNormal
    rw [cnfAdd_OmegaMul_principal, FreundTerm.cnfExponents_packCNF] at hExpNormal
    exact hExpNormal
  rw [cnfAdd_OmegaMul_principal, cnfAdd_OmegaMul_principal]
  exact FreundTerm.packCNF_lt_of_normal_list_lt hListA hListB hListLt

theorem FreundTermList_normal_append_of_bounded {as bs : List FreundTerm}
        (has : FreundTermList_normal as) (hbs : FreundTermList_normal bs)
        (hbound : ∀ a, a ∈ as → ∀ b, b ∈ bs → b ≤f a) :
        FreundTermList_normal (as ++ bs) := by
  induction as with
  | nil => simpa using hbs
  | cons a as ih =>
      cases as with
      | nil =>
          cases bs with
          | nil => simpa using has
          | cons b bs =>
              simp only [List.cons_append, List.nil_append]
              apply FreundTermList_normal.cons
              · exact FreundTerm.FreundTermList_normal_head has
              · exact hbs
              · intro t ht
                exact hbound a (by simp) t (by simp [ht])
      | cons a' as =>
          simp only [List.cons_append]
          apply FreundTermList_normal.cons
          · exact FreundTerm.FreundTermList_normal_head has
          · apply ih (FreundTerm.FreundTermList_normal_tail has)
            intro x hx b hb
            exact hbound x (by simp [hx]) b hb
          · intro z hz
            simp only [List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact FreundTerm.FreundTermList_normal_tail_bounded has _ (by simp)
            · rw [List.mem_append] at hz
              rcases hz with hz | hz
              · exact FreundTerm.FreundTermList_normal_tail_bounded has z (by simp [hz])
              · exact hbound a (by simp) z hz

theorem principal_normal_of_mem {p : _root_.principal} {ps : List _root_.principal}
        (hps : principalList_normal ps) (hp : p ∈ ps) : principal_normal p := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact NormalPrincipalList_normalHead hps
      · exact ih (NormalPrincipalList_normalTail hps) hp

theorem principal_cmplx_lt_of_mem {p : _root_.principal} {ps : List _root_.principal}
        (hp : p ∈ ps) : principal_cmplx p < principalList_cmplx ps := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp [principalList_cmplx]
      · have h := ih hp
        simp only [principalList_cmplx]
        omega

theorem omegaTerm_cmplx_ge_four (a : _root_.omegaTerm) : 4 ≤ omegaTerm_cmplx a := by
  cases a with
  | zero => simp [omegaTerm_cmplx]
  | omegaNF alpha beta gamma =>
      have hAlpha := omegaTerm_cmplx_ge_four alpha
      simp only [omegaTerm_cmplx]
      omega
  termination_by omegaTerm_cmplx a
  decreasing_by
    simp only [omegaTerm_cmplx]
    omega

theorem countableOrd_one_cmplx_le_of_pos {beta : _root_.countableOrd}
        (hbeta : countableOrd.zero <c beta) :
        countableOrd_cmplx countableOrd.one ≤ countableOrd_cmplx beta := by
  obtain ⟨p, ps, rfl⟩ := countable_zero_lt_nonempty hbeta
  cases p with
  | psi a =>
      have ha := omegaTerm_cmplx_ge_four a
      simp [countableOrd.one, countableOrd.ofPrincipal, principal.one,
        countableOrd_cmplx, principalList_cmplx, principal_cmplx,
        omegaTerm_cmplx]
      omega
theorem principal_cmplx_lt_countable_of_mem {p : _root_.principal}
        {ps : List _root_.principal} (hp : p ∈ ps) :
        principal_cmplx p < countableOrd_cmplx (.sum ps) := by
  have h := principal_cmplx_lt_of_mem hp
  simp only [countableOrd_cmplx]
  omega

theorem principal_head_cmplx_lt_countable (p : _root_.principal)
        (ps : List _root_.principal) :
        principal_cmplx p < countableOrd_cmplx (.sum (p :: ps)) := by
  simp only [countableOrd_cmplx, principalList_cmplx]
  omega

theorem omegaNF_cmplx_gt_eight (alpha : _root_.omegaTerm)
        (beta : _root_.countableOrd) (gamma : _root_.omegaTerm) :
        8 < omegaTerm_cmplx (.omegaNF alpha beta gamma) := by
  have hAlpha := omegaTerm_cmplx_ge_four alpha
  have hGamma := omegaTerm_cmplx_ge_four gamma
  simp only [omegaTerm_cmplx]
  omega

set_option maxRecDepth 2000 in
mutual
theorem omega_lt_map {a b : _root_.omegaTerm} (ha : omegaTerm_normal a) (hb : omegaTerm_normal b)
        (h : a <o b) : omega a <f omega b := by
  cases h with
  | @zero alpha gamma beta =>
      cases hb with
      | omegaNF hAlpha hBeta hGamma hpos hrem =>
          exact omega_zero_lt_omegaNF_map hpos
  | @exponent alpha1 alpha2 gamma1 gamma2 beta1 beta2 hAlpha =>
      have hWhole1 :
          FreundTerm_normal
            (omega
              (.omegaNF alpha1 beta1 gamma1)) :=
        omega_normal_map ha

      have hWhole2 :
          FreundTerm_normal
            (omega
              (.omegaNF alpha2 beta2 gamma2)) :=
        omega_normal_map hb

      cases ha with

      | omegaNF
          hAlpha1
          hBeta1
          hGamma1
          hpos1
          hrem1 =>

        cases hb with

        | omegaNF
            hAlpha2
            hBeta2
            hGamma2
            hpos2
            hrem2 =>

          have hAlphaMap :
              omega alpha1 <f omega alpha2 :=
            omega_lt_map
              hAlpha1
              hAlpha2
              hAlpha

          have hAlpha1MapNormal :
              FreundTerm_normal
                (omega alpha1) :=
            omega_normal_map hAlpha1

          have hAlpha2MapNormal :
              FreundTerm_normal
                (omega alpha2) :=
            omega_normal_map hAlpha2

          obtain ⟨p1, ps1, hBeta1Form⟩ :=
            countable_zero_lt_nonempty hpos1

          obtain ⟨p2, ps2, hBeta2Form⟩ :=
            countable_zero_lt_nonempty hpos2

          subst beta1
          subst beta2

          cases hBeta1 with

          | sum hps1 =>

            cases hBeta2 with

            | sum hps2 =>

              have hp1Normal :
                  principal_normal p1 :=
                NormalPrincipalList_normalHead hps1

              have hp2Normal :
                  principal_normal p2 :=
                NormalPrincipalList_normalHead hps2

              have hp1MapNormal :
                  FreundTerm_normal
                    (principal p1) :=
                principal_normal_map hp1Normal

              have hp2MapNormal :
                  FreundTerm_normal
                    (principal p2) :=
                principal_normal_map hp2Normal

              have hHead :
                  FreundTerm.cnfAdd
                      (FreundTerm.OmegaMul
                        (omega alpha1))
                      (principal p1)
                    <f
                  FreundTerm.cnfAdd
                      (FreundTerm.OmegaMul
                        (omega alpha2))
                      (principal p2) := by

                exact
                  cnfAdd_OmegaMul_principal_lt
                    hAlpha1MapNormal
                    hAlpha2MapNormal
                    hAlphaMap
                    p1
                    p2
                    hp1MapNormal
                    hp2MapNormal

              have hList1 :
                  FreundTermList_normal
                    (FreundTerm.shiftExponents
                        (FreundTerm.OmegaMul
                          (omega alpha1))
                        (countable
                          (.sum (p1 :: ps1))) ++
                      FreundTerm.cnfExponents
                        (omega gamma1)) := by

                have hh :=
                  FreundTerm.cnfExponents_normal
                    hWhole1

                simpa only [
                  omega_omegaNF,
                  FreundTerm.cnfExponents_packCNF
                ] using hh

              have hList2 :
                  FreundTermList_normal
                    (FreundTerm.shiftExponents
                        (FreundTerm.OmegaMul
                          (omega alpha2))
                        (countable
                          (.sum (p2 :: ps2))) ++
                      FreundTerm.cnfExponents
                        (omega gamma2)) := by

                have hh :=
                  FreundTerm.cnfExponents_normal
                    hWhole2

                simpa only [
                  omega_omegaNF,
                  FreundTerm.cnfExponents_packCNF
                ] using hh

              have hLists :
                  FreundTermList_lt
                    (FreundTerm.shiftExponents
                        (FreundTerm.OmegaMul
                          (omega alpha1))
                        (countable
                          (.sum (p1 :: ps1))) ++
                      FreundTerm.cnfExponents
                        (omega gamma1))
                    (FreundTerm.shiftExponents
                        (FreundTerm.OmegaMul
                          (omega alpha2))
                        (countable
                          (.sum (p2 :: ps2))) ++
                      FreundTerm.cnfExponents
                        (omega gamma2)) := by

                simp only [
                  FreundTerm.shiftExponents,
                  cnfExponents_countable_sum,
                  principalList,
                  List.map_cons,
                  List.cons_append
                ]

                exact
                  FreundTermList_lt.head hHead

              rw [
                omega_omegaNF,
                omega_omegaNF
              ]

              exact
                FreundTerm.packCNF_lt_of_normal_list_lt
                  hList1
                  hList2
                  hLists


  | @coefficient
      alpha1 alpha2 gamma1 gamma2 beta1 beta2
      hAlphaEq hBeta =>

      have hWhole1 :
          FreundTerm_normal
            (omega
              (.omegaNF alpha1 beta1 gamma1)) :=
        omega_normal_map ha

      have hWhole2 :
          FreundTerm_normal
            (omega
              (.omegaNF alpha2 beta2 gamma2)) :=
        omega_normal_map hb

      have hAlphaLean :
          alpha1 = alpha2 :=
        omegaTerm_eq_to_eq hAlphaEq

      subst alpha2

      cases ha with

      | omegaNF
          hAlpha1
          hBeta1
          hGamma1
          hpos1
          hrem1 =>

        cases hb with

        | omegaNF
            hAlpha2
            hBeta2
            hGamma2
            hpos2
            hrem2 =>

          have hAlphaMapNormal :
              FreundTerm_normal
                (omega alpha1) :=
            omega_normal_map hAlpha1

          have hBaseNormal :
              FreundTerm_normal
                (FreundTerm.OmegaMul
                  (omega alpha1)) :=
            FreundTerm.OmegaMul_normal
              hAlphaMapNormal

          have hBeta1MapNormal :
              FreundTerm_normal
                (countable beta1) :=
            countable_normal_map hBeta1

          have hBeta2MapNormal :
              FreundTerm_normal
                (countable beta2) :=
            countable_normal_map hBeta2

          have hBetaMap :
              countable beta1
                <f
              countable beta2 :=
            countable_lt_map
              hBeta1
              hBeta2
              hBeta

          have hShift :
              FreundTermList_lt
                (FreundTerm.shiftExponents
                  (FreundTerm.OmegaMul
                    (omega alpha1))
                  (countable beta1))
                (FreundTerm.shiftExponents
                  (FreundTerm.OmegaMul
                    (omega alpha1))
                  (countable beta2)) := by

            exact
              FreundTerm.shiftExponents_lt
                hBaseNormal
                hBeta1MapNormal
                hBeta2MapNormal
                hBetaMap

          have hCutoffLe :               ∀ t,
                t ∈
                  FreundTerm.shiftExponents
                    (FreundTerm.OmegaMul
                      (omega alpha1))
                    (countable beta2) →
                FreundTerm.cnfAdd
                    (FreundTerm.OmegaMul
                      (omega alpha1))
                    (principal
                      (_root_.principal.one))
                  ≤f
                t := by

            intro t ht

            unfold FreundTerm.shiftExponents at ht

            obtain ⟨e, he, rfl⟩ :=
              List.mem_map.mp ht

            obtain
              ⟨p, ps, hForm, hpMem, he⟩ :=
              countable_exponent_exists_principal he

            subst e

            have hBeta2Copy := hBeta2

            rw [hForm] at hBeta2Copy

            cases hBeta2Copy with

            | sum hps =>

              have hpNormal : principal_normal p :=
                principal_normal_of_mem hps hpMem

              have hpMapNormal :
                  FreundTerm_normal
                    (principal p) :=
                principal_normal_map hpNormal

              have hOneLe :
                  principal
                      (_root_.principal.one)
                    ≤f
                  principal p :=
                principal_one_le_map hpNormal

              rcases hOneLe with hlt | heq

              · exact Or.inl
                  (FreundTerm.cnfAdd_right_lt
                    hBaseNormal
                    principal_one_map_normal
                    hpMapNormal
                    hlt)

              · rw [heq]
                exact Or.inr rfl

          have hPowerNormal :
              omegaTerm_normal
                (.omegaNF
                  alpha1
                  countableOrd.one
                  .zero) := by

            apply omegaTerm_normal.omegaNF

            · exact hAlpha1

            · exact countableOrd_one_normal

            · exact omegaTerm_normal.zero

            · exact countableOrd_zero_lt_one

            · exact omegaTerm_lt.zero

          have hGammaBound :
              omega gamma1
                <f
              omega
                (.omegaNF
                  alpha1
                  countableOrd.one
                  .zero) :=
            omega_lt_map
              hGamma1
              hPowerNormal
              hrem1

          have hGammaMapNormal :
              FreundTerm_normal
                (omega gamma1) :=
            omega_normal_map hGamma1

          have hPowerMapNormal :
              FreundTerm_normal
                (omega
                  (.omegaNF
                    alpha1
                    countableOrd.one
                    .zero)) :=
            omega_normal_map hPowerNormal

          have hGammaExpLt :
              FreundTermList_lt
                (FreundTerm.cnfExponents
                  (omega gamma1))
                (FreundTerm.cnfExponents
                  (omega
                    (.omegaNF
                      alpha1
                      countableOrd.one
                      .zero))) :=
            FreundTerm.cnfExponents_lt
              hGammaMapNormal
              hPowerMapNormal
              hGammaBound

          have hPowerExp :
              FreundTerm.cnfExponents
                  (omega
                    (.omegaNF
                      alpha1
                      countableOrd.one
                      .zero))
                =
              [FreundTerm.cnfAdd
                (FreundTerm.OmegaMul
                  (omega alpha1))
                  (principal
                  (_root_.principal.one))] := by
            change FreundTerm.cnfExponents
                (omega (.omegaNF alpha1
                  (countableOrd.ofPrincipal _root_.principal.one) .zero)) = _
            rw [omega_omegaNF, FreundTerm.cnfExponents_packCNF]
            unfold FreundTerm.shiftExponents
            rw [countable_ofPrincipal]
            rfl

          have hGammaBelow :
              ∀ t,
                t ∈
                  FreundTerm.cnfExponents
                    (omega gamma1) →
                t
                  <f
                FreundTerm.cnfAdd
                  (FreundTerm.OmegaMul
                    (omega alpha1))
                  (principal
                    (_root_.principal.one)) := by

            intro t ht

            rw [hPowerExp] at hGammaExpLt

            exact
              FreundTerm.FreundTermList_mem_lt_singleton
                (FreundTerm.cnfExponents_normal
                  hGammaMapNormal)
                hGammaExpLt
                ht

          have hLists :
              FreundTermList_lt
                (FreundTerm.shiftExponents
                    (FreundTerm.OmegaMul
                      (omega alpha1))
                    (countable beta1) ++
                  FreundTerm.cnfExponents
                    (omega gamma1))
                (FreundTerm.shiftExponents
                    (FreundTerm.OmegaMul
                      (omega alpha1))
                    (countable beta2) ++
                  FreundTerm.cnfExponents
                    (omega gamma2)) := by

            exact
              FreundTerm.FreundTermList_lt_append_below
                hShift
                hCutoffLe
                hGammaBelow

          have hList1 :
              FreundTermList_normal
                (FreundTerm.shiftExponents
                    (FreundTerm.OmegaMul
                      (omega alpha1))
                    (countable beta1) ++
                  FreundTerm.cnfExponents
                    (omega gamma1)) := by

            have hh :=
              FreundTerm.cnfExponents_normal
                hWhole1

            simpa only [
              omega_omegaNF,
              FreundTerm.cnfExponents_packCNF
            ] using hh

          have hList2 :
              FreundTermList_normal
                (FreundTerm.shiftExponents
                    (FreundTerm.OmegaMul
                      (omega alpha1))
                    (countable beta2) ++
                  FreundTerm.cnfExponents
                    (omega gamma2)) := by

            have hh :=
              FreundTerm.cnfExponents_normal
                hWhole2

            simpa only [
              omega_omegaNF,
              FreundTerm.cnfExponents_packCNF
            ] using hh

          rw [
            omega_omegaNF,
            omega_omegaNF
          ]

          exact
            FreundTerm.packCNF_lt_of_normal_list_lt
              hList1
              hList2
              hLists


  | @remainder
      alpha1 alpha2 gamma1 gamma2 beta1 beta2
      hAlphaEq hBetaEq hGamma =>

      have hWhole1 :
          FreundTerm_normal
            (omega
              (.omegaNF alpha1 beta1 gamma1)) :=
        omega_normal_map ha

      have hWhole2 :
          FreundTerm_normal
            (omega
              (.omegaNF alpha2 beta2 gamma2)) :=
        omega_normal_map hb

      have hAlphaLean :
          alpha1 = alpha2 :=
        omegaTerm_eq_to_eq hAlphaEq

      have hBetaLean :
          beta1 = beta2 :=
        countableOrd_eq_to_eq hBetaEq

      subst alpha2
      subst beta2

      cases ha with

      | omegaNF
          hAlpha1
          hBeta1
          hGamma1
          hpos1
          hrem1 =>

        cases hb with

        | omegaNF
            hAlpha2
            hBeta2
            hGamma2
            hpos2
            hrem2 =>
          have hGammaMap : omega gamma1 <f omega gamma2 :=
               omega_lt_map hGamma1 hGamma2 hGamma

          have hGamma1MapNormal :
              FreundTerm_normal
                (omega gamma1) :=
            omega_normal_map hGamma1

          have hGamma2MapNormal :
              FreundTerm_normal
                (omega gamma2) :=
            omega_normal_map hGamma2

          have hGammaExp :
              FreundTermList_lt
                (FreundTerm.cnfExponents
                  (omega gamma1))
                (FreundTerm.cnfExponents
                  (omega gamma2)) :=
            FreundTerm.cnfExponents_lt
              hGamma1MapNormal
              hGamma2MapNormal
              hGammaMap

          have hLists :
              FreundTermList_lt
                (FreundTerm.shiftExponents
                    (FreundTerm.OmegaMul
                      (omega alpha1))
                    (countable beta1) ++
                  FreundTerm.cnfExponents
                    (omega gamma1))
                (FreundTerm.shiftExponents
                    (FreundTerm.OmegaMul
                      (omega alpha1))
                    (countable beta1) ++
                  FreundTerm.cnfExponents
                    (omega gamma2)) := by

            exact
              FreundTerm.FreundTermList_lt_append_left
                (FreundTerm.shiftExponents
                  (FreundTerm.OmegaMul
                    (omega alpha1))
                  (countable beta1))
                hGammaExp

          have hList1 :
              FreundTermList_normal
                (FreundTerm.shiftExponents
                    (FreundTerm.OmegaMul
                      (omega alpha1))
                    (countable beta1) ++
                  FreundTerm.cnfExponents
                    (omega gamma1)) := by

            have hh :=
              FreundTerm.cnfExponents_normal
                hWhole1

            simpa only [
              omega_omegaNF,
              FreundTerm.cnfExponents_packCNF
            ] using hh

          have hList2 :
              FreundTermList_normal
                (FreundTerm.shiftExponents
                    (FreundTerm.OmegaMul
                      (omega alpha1))
                    (countable beta1) ++
                  FreundTerm.cnfExponents
                    (omega gamma2)) := by

            have hh :=
              FreundTerm.cnfExponents_normal
                hWhole2

            simpa only [
              omega_omegaNF,
              FreundTerm.cnfExponents_packCNF
            ] using hh

          rw [
            omega_omegaNF,
            omega_omegaNF
          ]

          exact
            FreundTerm.packCNF_lt_of_normal_list_lt
              hList1
              hList2
              hLists
  termination_by omegaTerm_cmplx a + omegaTerm_cmplx b
  decreasing_by
    all_goals
      try have hAlphaC :=
        omegaTerm_cmplx_ge_four alpha

      try have hGammaC :=
        omegaTerm_cmplx_ge_four gamma

      try have hAlpha1C :=
        omegaTerm_cmplx_ge_four alpha1

      try have hAlpha2C :=
        omegaTerm_cmplx_ge_four alpha2

      try have hGamma1C :=
        omegaTerm_cmplx_ge_four gamma1

      try have hGamma2C :=
        omegaTerm_cmplx_ge_four gamma2

      subst_vars

      try have hposC :=
        countableOrd_one_cmplx_le_of_pos hpos

      try have hpos1C :=
        countableOrd_one_cmplx_le_of_pos hpos1

      try have hpos2C :=
        countableOrd_one_cmplx_le_of_pos hpos2

      try have hpMemC :=
        principal_cmplx_lt_of_mem hpMem

      try have hp1C :=
        principal_head_cmplx_lt_countable p1 ps1

      try have hp2C :=
        principal_head_cmplx_lt_countable p2 ps2

      simp only [
        omegaTerm_cmplx,
        countableOrd_cmplx,
        principalList_cmplx,
        principal_cmplx
      ] at *

      omega

-- Normal source omega terms translate to normal Freund terms.
theorem omega_normal_map {a : _root_.omegaTerm} (ha : omegaTerm_normal a) :
        FreundTerm_normal (omega a) := by
  cases ha with
  | zero =>
      rw [omega_zero]
      exact FreundTerm_normal.cnf FreundTermList_normal.nil (by simp)
  | @omegaNF alpha gamma beta hAlpha hBeta hGamma hpos hrem =>
      have hAlphaMapNormal : FreundTerm_normal (omega alpha) :=
        omega_normal_map hAlpha
      have hBetaMapNormal : FreundTerm_normal (countable beta) :=
        countable_normal_map hBeta
      have hGammaMapNormal : FreundTerm_normal (omega gamma) :=
        omega_normal_map hGamma
      have hBaseMapNormal : FreundTerm_normal (FreundTerm.OmegaMul (omega alpha)) :=
        FreundTerm.OmegaMul_normal hAlphaMapNormal
      have hShiftNormal :
          FreundTermList_normal
            (FreundTerm.shiftExponents
              (FreundTerm.OmegaMul (omega alpha))
              (countable beta)) :=
        FreundTerm.shiftExponents_normal hBaseMapNormal hBetaMapNormal
      have hGammaExponentsNormal :
          FreundTermList_normal (FreundTerm.cnfExponents (omega gamma)) :=
        FreundTerm.cnfExponents_normal hGammaMapNormal
      have hPowerNormal : omegaTerm_normal (.omegaNF alpha countableOrd.one .zero) := by
        exact omegaTerm_normal.omegaNF hAlpha countableOrd_one_normal
          omegaTerm_normal.zero countableOrd_zero_lt_one omegaTerm_lt.zero
      have hGammaBound :
          omega gamma <f omega (.omegaNF alpha countableOrd.one .zero) :=
        omega_lt_map hGamma hPowerNormal hrem
      have hPowerMapNormal :
          FreundTerm_normal
            (omega (.omegaNF alpha countableOrd.one .zero)) := by
        have hOneMapNormal :
            FreundTerm_normal (countable countableOrd.one) := by
          change FreundTerm_normal
            (countable (countableOrd.ofPrincipal _root_.principal.one))
          rw [countable_ofPrincipal]
          exact principal_one_map_normal
        have hPowerShiftNormal :
            FreundTermList_normal
              (FreundTerm.shiftExponents
                (FreundTerm.OmegaMul (omega alpha))
                (countable countableOrd.one)) :=
          FreundTerm.shiftExponents_normal hBaseMapNormal hOneMapNormal
        rw [omega_omegaNF]
        apply FreundTerm.packCNF_normal
        simpa [omega_zero, FreundTerm.cnfExponents] using hPowerShiftNormal
      have hGammaExponentsLt :
          FreundTermList_lt
            (FreundTerm.cnfExponents (omega gamma))
            (FreundTerm.cnfExponents
              (omega (.omegaNF alpha countableOrd.one .zero))) :=
        FreundTerm.cnfExponents_lt hGammaMapNormal hPowerMapNormal hGammaBound
      have hPowerExponents :
          FreundTerm.cnfExponents (omega (.omegaNF alpha countableOrd.one .zero)) =
            [FreundTerm.cnfAdd (FreundTerm.OmegaMul (omega alpha))
              (principal (_root_.principal.one))] := by
        change FreundTerm.cnfExponents
            (omega (.omegaNF alpha
              (countableOrd.ofPrincipal _root_.principal.one) .zero)) = _
        rw [omega_omegaNF, FreundTerm.cnfExponents_packCNF]
        unfold FreundTerm.shiftExponents; rw [countable_ofPrincipal]; rfl
      have hGammaBelow :
          ∀ t, t ∈ FreundTerm.cnfExponents (omega gamma) →
            t <f FreundTerm.cnfAdd
              (FreundTerm.OmegaMul (omega alpha))
              (principal (_root_.principal.one)) := by
        intro t ht
        rw [hPowerExponents] at hGammaExponentsLt
        exact FreundTerm.FreundTermList_mem_lt_singleton
          hGammaExponentsNormal hGammaExponentsLt ht
      have hShiftAbove :
          ∀ t,
            t ∈ FreundTerm.shiftExponents
              (FreundTerm.OmegaMul (omega alpha)) (countable beta) →
            FreundTerm.cnfAdd
                (FreundTerm.OmegaMul (omega alpha))
                (principal (_root_.principal.one)) ≤f t := by
        intro t ht
        unfold FreundTerm.shiftExponents at ht
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
        obtain ⟨p, ps, hForm, hpMem, rfl⟩ :=
          countable_exponent_exists_principal he
        have hBetaCopy := hBeta
        rw [hForm] at hBetaCopy
        cases hBetaCopy with
        | sum hps =>
            have hpNormal : principal_normal p :=
              principal_normal_of_mem hps hpMem
            rcases principal_one_le_map hpNormal with hlt | heq
            · exact Or.inl (FreundTerm.cnfAdd_right_lt hBaseMapNormal
                principal_one_map_normal (principal_normal_map hpNormal) hlt)
            · rw [heq]
              exact Or.inr rfl
      rw [omega_omegaNF]
      apply FreundTerm.packCNF_normal
      apply FreundTermList_normal_append_of_bounded
        hShiftNormal hGammaExponentsNormal
      intro s hs t ht
      exact FreundTerm.FreundTerm_le_trans
        (Or.inl (hGammaBelow t ht))
        (hShiftAbove s hs)
  termination_by omegaTerm_cmplx a + 8
  decreasing_by
    all_goals
      subst_vars
      try have hAlphaC := omegaTerm_cmplx_ge_four alpha
      try have hGammaC := omegaTerm_cmplx_ge_four gamma
      try have hposC := countableOrd_one_cmplx_le_of_pos hpos
      try have hpMemC := principal_cmplx_lt_of_mem hpMem
      simp only [
        omegaTerm_cmplx,
        countableOrd_cmplx,
        principalList_cmplx,
        principal_cmplx
      ] at *
      omega

-- Strict comparison of normal source principals is preserved by the Freund translation.
theorem principal_lt_map {p q : _root_.principal}
    (hp : principal_normal p)
    (hq : principal_normal q)
    (h : p<pq) :
    principal p <f principal q := by
  cases p with
  | psi a =>
      cases q with
      | psi b =>
          cases hp with
          | psi ha hCoeffA =>
            cases hq with
            | psi hb hCoeffB =>
              rw [principal_psi, principal_psi]

              cases h with

              | psi_forward hab hCoeff =>
                  apply FreundTerm_lt.theta_theta_forward

                  · exact omega_lt_map ha hb hab

                  · intro g hg

                    obtain ⟨c, hc, p, ps, hForm, hpMem, rfl⟩ :=
                      E_omega_exists_coefficient hg

                    have hcNormal : countableOrd_normal c :=
                      coefficient_normal_of_mem ha hc

                    rw [hForm] at hcNormal

                    cases hcNormal with

                    | sum hps =>
                        have hpNormal : principal_normal p :=
                          principal_normal_of_mem hps hpMem

                        have hcb :
                            c <c countableOrd.ofPrincipal (.psi b) :=
                          coefficientList_lt_of_mem hCoeff hc

                        have hpb : p <p .psi b :=
                          coefficient_component_lt_principal hps
                            (by simpa [hForm] using hcb) hpMem

                        exact principal_lt_map
                          hpNormal
                          (principal_normal.psi hb hCoeffB)
                          hpb
              | @psi_reverse_lt _ _ c hba hc hac =>
                  have hcNormal : countableOrd_normal c := coefficient_normal_of_mem hb hc
                  obtain ⟨p, ps, hForm, hpMem, hap⟩ := principal_le_countable_exists_component
                         hcNormal (Or.inl hac)
                  have hpNormal : principal_normal p := by
                    rw [hForm] at hcNormal
                    cases hcNormal with
                    | sum hps => exact principal_normal_of_mem hps hpMem
                  have hpE : principal p ∈ FreundTerm.E (omega b) :=
                    coefficient_principal_mem_E_omega hb hc hForm hpMem
                  rcases hap with hap | hap
                  · exact FreundTerm_lt.theta_theta_support_lt hpE
                          (principal_lt_map (principal_normal.psi ha hCoeffA) hpNormal hap)
                  · have hEq : (.theta (omega a) : FreundTerm) = principal p :=
                      principal_eq_map_eq hap
                    rw [hEq]
                    have hSupport : principal p <f (.theta (omega b) : FreundTerm) := by
                      cases p with
                      | psi d =>
                          apply FreundTerm_lt.theta_theta_support_eq
                          simpa [principal] using hpE
                    exact hSupport
              | @psi_reverse_eq _ _ c hba hc hac =>
                  have hcNormal : countableOrd_normal c :=
                    coefficient_normal_of_mem hb hc

                  obtain ⟨p, ps, hForm, hpMem, hap⟩ := principal_le_countable_exists_component
                         hcNormal (Or.inr hac)
                  have hpNormal : principal_normal p := by
                    rw [hForm] at hcNormal
                    cases hcNormal with
                    | sum hps => exact principal_normal_of_mem hps hpMem
                  have hpE : principal p ∈ FreundTerm.E (omega b) :=
                    coefficient_principal_mem_E_omega hb hc hForm hpMem
                  rcases hap with hap | hap
                  · exact FreundTerm_lt.theta_theta_support_lt hpE
                          (principal_lt_map (principal_normal.psi ha hCoeffA) hpNormal
                          hap)
                  · have hEq : (.theta (omega a) : FreundTerm) = principal p :=
                      principal_eq_map_eq hap
                    rw [hEq]
                    have hSupport : principal p <f (.theta (omega b) : FreundTerm) := by
                      cases p with
                      | psi d =>
                          apply FreundTerm_lt.theta_theta_support_eq
                          simpa [principal] using hpE
                    exact hSupport
  termination_by principal_cmplx p + principal_cmplx q
  decreasing_by
    all_goals
      subst_vars
      try have hcC := coefficient_cmplx_lt_of_mem hc
      try have hpMemC := principal_cmplx_lt_of_mem hpMem
      simp only [
        principal_cmplx,
        countableOrd_cmplx,
        principalList_cmplx
      ] at *
      omega


theorem principal_normal_map {p : _root_.principal} (hp : principal_normal p) :
        FreundTerm_normal (principal p) := by
  cases hp with
  | psi harg hcoeff => rw [principal_psi]; exact FreundTerm_normal.theta (omega_normal_map harg)
  termination_by principal_cmplx p + 8
  decreasing_by
    all_goals
      subst_vars
      simp only [principal_cmplx]
      omega

theorem principal_le_map {p q : _root_.principal} (hp : principal_normal p)
        (hq : principal_normal q) (h : p ≤p q) :
        principal p ≤f principal q := by
  rcases h with h | h
  · exact Or.inl (principal_lt_map hp hq h)
  · exact Or.inr (principal_eq_map_eq h)
  termination_by principal_cmplx p + principal_cmplx q + 1
  decreasing_by
    all_goals
      omega


theorem principalList_normal_map {ps : List _root_.principal} (hps : principalList_normal ps) :
        FreundTermList_normal (principalList ps) := by
  cases ps with
  | nil => exact FreundTermList_normal.nil
  | cons p ps =>
      cases ps with
      | nil =>
          cases hps with
          | singleton hp =>
              exact FreundTermList_normal.single (principal_normal_map hp)
      | cons q qs =>
          cases hps with
          | cons hp htail hpq =>
              simp only [principalList]
              apply FreundTermList_normal.cons
              · exact principal_normal_map hp
              · exact principalList_normal_map htail
              · intro t ht
                change t ∈ principalList (q :: qs) at ht
                rw [principalList_eq_map] at ht
                obtain ⟨r, hr, rfl⟩ :=
                  List.mem_map.mp ht
                exact
                  principal_le_map
                    (principal_normal_of_mem htail hr)
                    hp
                    (principalList_normal_tail_bounded
                      (principalList_normal.cons hp htail hpq)
                      r
                      (by simp [hr]))
  termination_by principalList_cmplx ps + 8
  decreasing_by
    all_goals
      subst_vars
      try have hrC :=
        principal_cmplx_lt_of_mem hr
      simp only [principalList_cmplx, principal_cmplx] at *
      omega


theorem principalList_lt_map
    {ps qs : List _root_.principal}
    (hps : principalList_normal ps)
    (hqs : principalList_normal qs)
    (h : principalList_lt ps qs) :
    FreundTermList_lt
      (principalList ps)
      (principalList qs) := by
  cases h with
  | nil =>
      simp only [principalList]
      exact FreundTermList_lt.nil

  | head hpq =>
      simp only [principalList]
      exact
        FreundTermList_lt.head
          (principal_lt_map
            (NormalPrincipalList_normalHead hps)
            (NormalPrincipalList_normalHead hqs)
            hpq)

  | tail hpq htail =>
      simp only [principalList]
      rw [principal_eq_map_eq hpq]
      exact
        FreundTermList_lt.tail
          (principalList_lt_map
            (NormalPrincipalList_normalTail hps)
            (NormalPrincipalList_normalTail hqs)
            htail)

  termination_by
    principalList_cmplx ps +
      principalList_cmplx qs

  decreasing_by
    all_goals
      subst_vars
      simp only [principalList_cmplx]
      omega


theorem countable_lt_map
    {a b : _root_.countableOrd}
    (ha : countableOrd_normal a)
    (hb : countableOrd_normal b)
    (h : a <c b) :
    countable a <f countable b := by
  cases ha with
  | sum hps =>
    cases hb with
    | sum hqs =>
      cases h with
      | sum hlists =>
          rw [countable_sum, countable_sum]
          exact
            FreundTerm.packCNF_lt_of_normal_list_lt
              (principalList_normal_map hps)
              (principalList_normal_map hqs)
              (principalList_lt_map hps hqs hlists)

  termination_by
    countableOrd_cmplx a +
      countableOrd_cmplx b + 8

  decreasing_by
    all_goals
      subst_vars
      simp only [countableOrd_cmplx]
      omega


theorem countable_normal_map
    {a : _root_.countableOrd}
    (ha : countableOrd_normal a) :
    FreundTerm_normal (countable a) := by
  cases ha with
  | sum hps =>
      rw [countable_sum]
      exact
        FreundTerm.packCNF_normal
          (principalList_normal_map hps)

  termination_by
    countableOrd_cmplx a + 8

  decreasing_by
    all_goals
      subst_vars
      simp only [countableOrd_cmplx] at *
      omega

end
-- Strict comparison of normal source omega terms is preserved by the Freund translation.
end BHToFreund

namespace BHToFreund
-- Map NormalPrincipal into NormalFreundTerm.
noncomputable def NormalPrincipal_toFreund (p : NormalPrincipal) : NormalFreundTerm :=
  ⟨principal p.1, principal_normal_map p.2⟩
-- NormalPrincipal comparison is preserved by the map to NormalFreundTerm.
theorem NormalPrincipal_toFreund_lt {p q : NormalPrincipal} (h : p<npq) :
        NormalFreundTerm_lt (NormalPrincipal_toFreund p) (NormalPrincipal_toFreund q) := by
  change principal p.1 <f principal q.1
  exact principal_lt_map p.2 q.2 h
end BHToFreund

--=========================================================================================
-- GapTreeEmbeds, WellQuasiOrdered
--=========================================================================================
/- Proof Outline :
   If GapTreeEmbeds is well-quasi-ordered, given any infinite sequence of gap trees, some
   earlier tree embeds into some later tree. Formally, if T₀, T₁, ..., then there must
   exist indices i < j such that GapTreeEmbeds T_i T_j. Recall the two cases of when a
   gap tree embeds into another. (Root) The root case is when the root label is the same
   and given subtrees [A, B] and the other tree with [X, Y, Z], A embeds into X and
   B embeds into Y for example. (Descend) The descend case is, say we have two tree T₁ and T₂.
   Then, given conditions that the (root label of T₁) ≤ (root label of T₂) -- this is the strong
   gap restriction -- and the entire T₁embeds into some child of T₂, then T₁ embeds into T₂.
   The complicated case is when it descend several levels. Suppose s has root 1, s embeds into u,
   and u is buried deep in t :
                  1             1
                  |             |
                  v             v
                  |             |
                  1             0
                  |             |
                  w             w
                  |             |
                  1             1
                  |             |
                  u             u
   For the left case, s embeds into u → s embeds into parent of u → s embeds into parent of parent
   of u. But the right hand case has a 0, making it not satisfy the strong gap condition. So, we
   must have a theorem like "u occers properly below t, and the path from t down toward u is
   compatible with a source whose root label is k." Or, every parent that we would need to climb
   through satisfies k ≤ parent label.
   1. Separate two cases for the root labels
   2. Formalize the strong-gap restriction (admissible descendants)
   3. Connect 2. with embedding
   4. Bad sequence
   As commonly, we prove wqo with contradiction. In such case, we must have that there exists some
   f : ℕ → GapTree such that ∀ i, j, i < j → ¬ GapTreeEmbeds (f i) (f j). We call this the "bad
   sequence"
-/
instance GapTreeEmbeds_isPreorder : IsPreorder GapTree GapTreeEmbeds where
  refl := GapTreeEmbeds_refl
  trans := by intro a b c hab hbc; exact GapTreeEmbeds_trans hab hbc
/- Root Classes -/
namespace GapTree
def RootIs (k : GapLabel) : Set GapTree := {t | rootLabel t = k}
def RootAtLeast (k : GapLabel) : Set GapTree := {t | k ≤ rootLabel t}
end GapTree
/- Admissible Descendants -/
namespace GapTree
/- u is a proper descendant of t, and every node we pass through on the way from u up to t has
   label at least k -/
inductive AdmissibleDescendant (k : GapLabel) : GapTree → GapTree → Prop where
  -- The case when u is an immediate child of the larger tree
  | child {u : GapTree} {n : GapLabel} {before after : List GapTree} (hlabel : k ≤ n) :
    AdmissibleDescendant k u (.node n (before ++ u :: after))
  -- The other case : if u is admissible in v rootlabel(t)≥k
  | step {u v : GapTree} {n : GapLabel} {before after : List GapTree} (hlabel : k ≤ n)
         (h : AdmissibleDescendant k u v) :
    AdmissibleDescendant k u (.node n (before ++ v :: after))
-- Admissible descendants are strictly smaller in complexity
theorem AdmissibleDescendant_transComplexity_lt {k : GapLabel} {u t : GapTree}
        (h : AdmissibleDescendant k u t) :
        transComplexity u < transComplexity t := by
  induction h <;>
    simp_all [transComplexity, transComplexityList, transComplexityList_append] <;>
    omega
-- If s embeds into u and u sits admissibly below t, then s embeds into t
/- Given s embeds into u and tree
    t
    |
   ...
    |
    u
-/
theorem GapTreeEmbeds_descend_admissible {k : GapLabel} {s u t : GapTree}
        (hs : s ∈ RootIs k) (hsu : GapTreeEmbeds s u)
        (hut : AdmissibleDescendant k u t) :
        GapTreeEmbeds s t := by
  have hsRoot : rootLabel s = k := hs
  induction hut with
  | child hlabel => apply GapTreeEmbeds.descend
                    · rw [hsRoot]; exact hlabel
                    · exact hsu
  | step hlabel h ih => apply GapTreeEmbeds.descend
                        · rw [hsRoot]; exact hlabel
                        · exact ih
-- Bad Sequences
-- ∀ n ∈ ℕ, (f n) ∈ S and ∀ m n, m < n → ¬ GapTreeEmbeds (f m) (f n)
abbrev GapBadSeq (S : Set GapTree) (f : ℕ → GapTree) : Prop :=
  Set.PartiallyWellOrderedOn.IsBadSeq GapTreeEmbeds S f
/- At position n, f n cannot be replaced by a tree of strictly smaller transComplexity,
   while keeping all positions before n unchanged, and still have a bad sequence
   ∀ g, (∀ m < n, f m = g n) → GapTree.transComplexity (g n) < GapTree.transComplexity (f n)
   → ¬ GapBadSeq S g -/
abbrev GapMinBadSeq (S : Set GapTree) (n : ℕ) (f : ℕ → GapTree) : Prop :=
  Set.PartiallyWellOrderedOn.IsMinBadSeq GapTreeEmbeds GapTree.transComplexity S n f
-- Simply retrieving the information from bad sequnces
theorem GapBadSeq_mem {S : Set GapTree} {f : ℕ → GapTree} (h : GapBadSeq S f) {m n : ℕ}
        (hmn : m < n) : f n ∈ S := by
  exact h.1 n
theorem GapBadSeq_not_embeds {S : Set GapTree} {f : ℕ → GapTree} (h : GapBadSeq S f) {m n : ℕ}
        (hmn : m < n) : ¬ GapTreeEmbeds (f m) (f n) := by
  exact h.2 m n hmn
/- Given sequence f = T₀, T₁, ..., T_n, ... and assuming f n is minimal, replacing f n with g n,
   which has a smaller comlexity does not make the sequnce a bad one as that will contradict
   f n being minimal. -/
theorem GapMinBadSeq_no_smaller_bad {S : Set GapTree} {f g : ℕ → GapTree} {n : ℕ}
        (hmin : GapMinBadSeq S n f) (hprefix : ∀ m < n, f m = g m)
        (hsmall : GapTree.transComplexity (g n) < GapTree.transComplexity (f n)) :
        ¬ GapBadSeq S g := by
  exact hmin g hprefix hsmall
-- Existence of the minimal bad sequnce
theorem exists_GapMinBadSeq {S : Set GapTree} (hbad : ∃ f : ℕ → GapTree, GapBadSeq S f) :
        ∃ f : ℕ → GapTree, GapBadSeq S f ∧ ∀ n, GapMinBadSeq S n f := by
  exact Set.PartiallyWellOrderedOn.exists_min_bad_of_exists_bad
        GapTreeEmbeds GapTree.transComplexity S hbad
end GapTree
/- The important step in proving WQO of GapTreeEmbeds we take is Higman's lemma. The lemma says
   for finite lists over A, define the Higman embedding relation [a₁, ..., a_m] ≤H [b₁, ..., b_n]
   iff there are indices 1 ≤ i₁ ≤ ... ≤ i_m ≤ n such that a_j ≤A b_{i_j} for every j. In our
   GapTree notations, say we want to adapt the finite list Higman discusses to our List GapTree.
   For example, given .node label0 [A, B, C], [A, B, C] ≤H [W, X, Y, Z] if the target positions
   are incresing with the GapTreeEmbed process. So, A embedding in W, B embedding in Y, and C
   embedding in Z is premitted by if such order is not preserved, the Higman lemma cannot be used,
   as our List GapTree does not have order. So, if we think of the Higman relation as R_H and
   the embedding of ours as R_G, we have R_H ⊆ R_G. Since the condition for "relation R is WQO"
   is that for every infinite sequence x₀, x₁,... there exist indices i < j such that R(x_i, x_j).
   Since R_H ⊆ R_G, R_H(x_i, x_j) implies R_G(x_i, x_j) and thus, R_H is WQO and R_H ⊆ R_G iplies
   R_G is WQO. The LEAN mathlib already provides statement "S is WQO as individual trees →
   finite forests made from S are WQO." So, the proof flow would be
   1. Assume, towards contradiction, there is a bad sequnce of GapTrees,
      i.e., there exist i < j such that GapTreeEmbeds (f i) (f j)
      ↓
   2. By existence assured, choose the minimal bad sequence f
      ↓
   3. For proper adimissble descendants of f, minimality shows those form a WQO set S
      ↓
   4. By Higman, forests made from tress in S are WQO
      ↓
   5. two child forests embed and root
      ↓
   6. Two ordinal trees embed and contradiction -/
namespace GapTree
-- Every tree appearin in forest ts lies in S
def GapForestOn (S : Set GapTree) (ts : List GapTree) : Prop :=
  ∀ t, t ∈ ts → t ∈ S
-- Mathlib's ordered Higman embedding implies unordered forest embedding
theorem GapForestEmbeds_of_sublistForall₂ {ss ts : List GapTree}
        (h : List.SublistForall₂ GapTreeEmbeds ss ts) :
        GapForestEmbeds ss ts := by
  -- Concept of List.sublistForall₂
  -- to mean List.SublistForall₂ R l₁ l₂ → ∃ l, ListForall₂ l₁ l ∧ l.Sublist l₂
  /- List.SublistForall₂ R xs ys to mean you can choose a sublist of ys, in the same order, so that
     each element of xs is R-related to the corresponding chosen element. For example,
     List.SublistForall₂ ≤ [2, 5] [1, 3, 4, 7] is true
     becayse there exists a sublist [3, 7] such that 2 ≤ 3 and 5 ≤ 7. -/
  induction h with
  | nil => exact GapForestEmbeds.nil
  | cons hst hrest ih =>
      simpa using (GapForestEmbeds.cons (before := []) hst ih)
  | @cons_right t ss ts hrest ih => exact GapForestEmbeds_weaken_cons ih t
/- If the set of GapTrees S is partially well-ordered by GapTreeEmbeds, then the set of list of
   GapTrees ts such that every t ∈ ts satisfies t ∈ S is partially well-ordered by
   GapTreeEmbeds.
   hS : every infinite sequence of trees lying in S has some i < j such that f i embeds into f j -/
theorem GapForestEmbeds_partiallyWellOrderedOn {S : Set GapTree}
        (hS : S.PartiallyWellOrderedOn GapTreeEmbeds) :
        {ts : List GapTree | GapForestOn S ts}.PartiallyWellOrderedOn GapForestEmbeds := by
  have hHigman := Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ GapTreeEmbeds hS
  -- finite list whose entires lie in S are WQO under List.SublistForall₂ GapTreeEmbeds
  rw [Set.partiallyWellOrderedOn_iff_exists_lt] at hHigman ⊢
  intro f hf
  obtain ⟨i, j, hij, hsub⟩ := hHigman f hf
  exact ⟨i, j, hij, GapForestEmbeds_of_sublistForall₂ hsub⟩
end GapTree
--=================================================================================================
-- Kruskal Trees
--=================================================================================================
/- We introduce a concept that is already proven to be well-quasi-ordered : the Kruskal tree.
   Kruskal's theorem says roughly if the possible base labels X are WQO, then finite trees
   constructed from X are also WQO under tree embedding. So, (X,r) is WQO → (KruskalTree(X),
   KruskalTreeEmbeds(r)) is WQO.
   base x to mean simply just x
   node [t₀, t₁, ..., t_n] to mean
           (node)
          /  |  \
         t₀ ... t_n
   Our GapTree is simply a Kruskal Tree with an extra condition of strong gap restriction. Fruend,
   in his paper, introduces the idea that the gap condition can be reconstructed by iterated
   applications of uniform Kruskal theorem.
-/
inductive KruskalTree (X : Type) where
  | base : X → KruskalTree X
  | node : List (KruskalTree X) → KruskalTree X
mutual
inductive KruskalTreeEmbeds {X : Type} (r : X → X → Prop) :
          KruskalTree X → KruskalTree X → Prop where
  | base {x y : X} (h : r x y) : KruskalTreeEmbeds r (.base x) (.base y)
  -- Root same but the children embed w.r.t. KruskalForestEmbeds
  | root {ss ts : List (KruskalTree X)} (h : KruskalForestEmbeds r ss ts) :
      KruskalTreeEmbeds r (.node ss) (.node ts)
  --
  | descend {s t : KruskalTree X} {before after : List (KruskalTree X)}
            (h : KruskalTreeEmbeds r s t) :
    KruskalTreeEmbeds r s (.node (before ++ t :: after))
inductive KruskalForestEmbeds {X : Type} (r : X → X → Prop) :
          List (KruskalTree X) → List (KruskalTree X) → Prop where
  | nil {ts : List (KruskalTree X)} : KruskalForestEmbeds r [] ts
  | cons {s t : KruskalTree X} {ss before after : List (KruskalTree X)}
         (hst : KruskalTreeEmbeds r s t)
         (hrest : KruskalForestEmbeds r ss (before ++ after)) :
    KruskalForestEmbeds r (s :: ss) (before ++ t :: after)
end
-- Reflexive
mutual
theorem KruskalTreeEmbeds_refl {X : Type} {r : X → X → Prop} [IsPreorder X r] (t : KruskalTree X) :
        KruskalTreeEmbeds r t t := by
  cases t with
  | base x => exact KruskalTreeEmbeds.base (refl x)
  | node xs => apply KruskalTreeEmbeds.root; exact KruskalForestEmbeds_refl xs
theorem KruskalForestEmbeds_refl {X : Type} {r : X → X → Prop} [IsPreorder X r]
        (ts : List (KruskalTree X)) :
        KruskalForestEmbeds r ts ts := by
  cases ts with
  | nil => exact KruskalForestEmbeds.nil
  | cons t ts =>
    have ht : KruskalTreeEmbeds r t t := KruskalTreeEmbeds_refl t
    have hts : KruskalForestEmbeds r ts ts := KruskalForestEmbeds_refl ts
    simpa using (KruskalForestEmbeds.cons (s := t) (t := t) (ss := ts) (before := [])
                 (after := ts) ht hts)
end
-- If s embeds into t, then s embeds into any node having t as a child
theorem KruskalTreeEmbeds_into_parent {X : Type} {r : X → X → Prop} {s t : KruskalTree X}
        {before after : List (KruskalTree X)} (h : KruskalTreeEmbeds r s t) :
        KruskalTreeEmbeds r s (.node (before ++ t :: after)) := by
  exact KruskalTreeEmbeds.descend h
-- Adding a tree to a list of tree ts where a forest already embeds, it still embeds
theorem KruskalForestEmbeds_weaken_cons {X : Type} {r : X → X → Prop}
        {ss ts : List (KruskalTree X)} (h : KruskalForestEmbeds r ss ts)
        (u : KruskalTree X) : KruskalForestEmbeds r ss (u :: ts) := by
  cases h with
  | nil => exact KruskalForestEmbeds.nil
  | @cons s t ss before after hst hrest =>
    apply KruskalForestEmbeds.cons (s := s) (t := t) (ss := ss) (before := u :: before)
          (after := after)
    · exact hst
    · simpa using KruskalForestEmbeds_weaken_cons hrest u
-- Adding a prefix
theorem KruskalForestEmbeds_weaken_prefix {X : Type} {r : X → X → Prop}
        {ss ts : List (KruskalTree X)} (h : KruskalForestEmbeds r ss ts)
        (us : List (KruskalTree X)) :
        KruskalForestEmbeds r ss (us ++ ts) := by
  induction us with
  | nil => simpa using h
  | cons u us ih => simpa using KruskalForestEmbeds_weaken_cons ih u
-- Adding a suffix
theorem KruskalForestEmbeds_weaken_suffix {X : Type} {r : X → X → Prop}
        {ss ts : List (KruskalTree X)} (h : KruskalForestEmbeds r ss ts)
        (us : List (KruskalTree X)) :
        KruskalForestEmbeds r ss (ts ++ us) := by
  cases h with
  | nil => exact KruskalForestEmbeds.nil
  | @cons s t ss before after hst hrest =>
      have hrest' : KruskalForestEmbeds r ss (before ++ (after ++ us)) := by
        simpa [List.append_assoc] using KruskalForestEmbeds_weaken_suffix hrest us
      have hcons : KruskalForestEmbeds r (s :: ss)
                   (before ++ t :: (after ++ us)) := by
        exact KruskalForestEmbeds.cons (s := s) (t := t) (ss := ss)
              (before := before) (after := after ++ us) hst hrest'
      simpa [List.append_assoc] using hcons
-- Adding for both ends
theorem KruskalForestEmbeds_weaken {X : Type} {r : X → X → Prop}
        {ss ts : List (KruskalTree X)} (h : KruskalForestEmbeds r ss ts)
        (before after : List (KruskalTree X)) :
        KruskalForestEmbeds r ss (before ++ ts ++ after) := by
  have hprefix : KruskalForestEmbeds r ss (before ++ ts) :=
    KruskalForestEmbeds_weaken_prefix h before
  exact KruskalForestEmbeds_weaken_suffix hprefix after
/- If a tree is a member of a forest that embeds into another forest, the tree embeds
   into some member of the last forest -/
theorem KruskalForestEmbeds_exists_of_mem {X : Type} {r : X → X → Prop}
        {ss ts : List (KruskalTree X)} (h : KruskalForestEmbeds r ss ts)
        {s : KruskalTree X} (hs : s ∈ ss) :
        ∃ t, t ∈ ts ∧ KruskalTreeEmbeds r s t := by
  cases h with
  | nil => simp at hs
  | @cons s' t' ss before after hst hrest =>
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · refine ⟨t', ?_, hst⟩; simp
    · obtain ⟨t, ht, hst'⟩ := KruskalForestEmbeds_exists_of_mem hrest hs
      refine ⟨t, ?_, hst'⟩
      simp only [List.mem_append, List.mem_cons] at ht ⊢
      rcases ht with ht | ht
      · exact Or.inl ht
      · exact Or.inr (Or.inr ht)
-- Spotting the target tree in a forest
theorem KruskalForestEmbeds_head {X : Type} {r : X → X → Prop} {s : KruskalTree X}
        {ss ts : List (KruskalTree X)} (h : KruskalForestEmbeds r (s :: ss) ts) :
        ∃ t before after, ts = before ++ t :: after ∧ KruskalTreeEmbeds r s t ∧
                          KruskalForestEmbeds r ss (before ++ after) := by
  cases h with
  | @cons s t ss before after hst hrest =>
    exact ⟨t, before, after, rfl, hst, hrest⟩
-- Rewrites a list with a distinguished middle element as a multiset with that element singled out.
theorem Kruskal_multiset_coe_middle {X : Type} (before after : List (KruskalTree X))
        (t : KruskalTree X) :
        (↑(before ++ (t :: after)) : Multiset (KruskalTree X)) =
          t ::ₘ (↑(before ++ after) : Multiset (KruskalTree X)) := by
  rw [← Multiset.coe_add before (t :: after)]
  rw [← Multiset.coe_add before after]
  rw [← Multiset.cons_coe t after]
  rw [← Multiset.singleton_add t (↑after : Multiset (KruskalTree X))]
  rw [← Multiset.singleton_add t
    ((↑before : Multiset (KruskalTree X)) +
      (↑after : Multiset (KruskalTree X)))]
  ac_rfl
-- Converts a Kruskal forest embedding into a multiset matching contained in the target multiset.
theorem KruskalForestEmbeds_to_multiset {X : Type} {r : X → X → Prop} {ss ts : List (KruskalTree X)}
        (h : KruskalForestEmbeds r ss ts) :
        ∃ us : Multiset (KruskalTree X), Multiset.Rel (KruskalTreeEmbeds r)
         (↑ss : Multiset (KruskalTree X)) us ∧ us ≤ (↑ts : Multiset (KruskalTree X)) := by
  cases h with
  | nil => exact ⟨0, Multiset.Rel.zero, Multiset.zero_le _⟩
  | @cons s t ss before after hst hrest =>
      obtain ⟨us, hrel, hle⟩ := KruskalForestEmbeds_to_multiset hrest
      refine ⟨t ::ₘ us, ?_, ?_⟩
      · simpa using Multiset.Rel.cons hst hrel
      · rw [Kruskal_multiset_coe_middle before after t]
        exact Multiset.cons_le_cons t hle


-- Reconstructs a Kruskal forest embedding from a multiset matching contained in the target forest.
theorem KruskalForestEmbeds_of_multiset {X : Type} {r : X → X → Prop} {ss ts : List (KruskalTree X)}
        (h : ∃ us : Multiset (KruskalTree X), Multiset.Rel (KruskalTreeEmbeds r)
              (↑ss : Multiset (KruskalTree X)) us ∧ us ≤ (↑ts : Multiset (KruskalTree X))) :
        KruskalForestEmbeds r ss ts := by
  induction ss generalizing ts with
  | nil => exact KruskalForestEmbeds.nil
  | cons s ss ih =>
      obtain ⟨us, hrel, hle⟩ := h
      change Multiset.Rel (KruskalTreeEmbeds r) (s ::ₘ (↑ss : Multiset (KruskalTree X))) us
        at hrel
      obtain ⟨t, us', hst, hrel', hus⟩ := Multiset.rel_cons_left.mp hrel
      rw [hus] at hle
      have htM : t ∈ (↑ts : Multiset (KruskalTree X)) :=
        Multiset.mem_of_le hle (Multiset.mem_cons_self t us')
      have ht : t ∈ ts := by simpa using htM
      obtain ⟨before, after, hts⟩ := List.append_of_mem ht
      rw [hts] at hle
      rw [Kruskal_multiset_coe_middle before after t] at hle
      have hle' : us' ≤ (↑(before ++ after) : Multiset (KruskalTree X)) :=
        (Multiset.cons_le_cons_iff t).mp hle
      have hrest : KruskalForestEmbeds r ss (before ++ after) :=
        ih ⟨us', hrel', hle'⟩
      rw [hts]
      exact KruskalForestEmbeds.cons hst hrest
-- Removes one chosen source tree and its matched target tree while preserving the remaining
-- forest embedding.
theorem KruskalForestEmbeds_extract {X : Type} {r : X → X → Prop}
        {before after : List (KruskalTree X)} {s : KruskalTree X} {ts : List (KruskalTree X)}
        (h : KruskalForestEmbeds r (before ++ (s :: after)) ts) :
        ∃ t before' after', ts = before' ++ (t :: after') ∧ KruskalTreeEmbeds r s t ∧
          KruskalForestEmbeds r (before ++ after) (before' ++ after') := by
  obtain ⟨us, hrel, hle⟩ := KruskalForestEmbeds_to_multiset h
  rw [Kruskal_multiset_coe_middle before after s] at hrel
  obtain ⟨t, us', hst, hrel', hus⟩ := Multiset.rel_cons_left.mp hrel
  rw [hus] at hle
  have htM : t ∈ (↑ts : Multiset (KruskalTree X)) :=
    Multiset.mem_of_le hle (Multiset.mem_cons_self t us')
  have ht : t ∈ ts := by simpa using htM
  obtain ⟨before', after', hts⟩ := List.append_of_mem ht
  rw [hts] at hle
  rw [Kruskal_multiset_coe_middle before' after' t] at hle
  have hle' : us' ≤ (↑(before' ++ after') : Multiset (KruskalTree X)) :=
    (Multiset.cons_le_cons_iff t).mp hle
  have hrest : KruskalForestEmbeds r (before ++ after) (before' ++ after') :=
    KruskalForestEmbeds_of_multiset ⟨us', hrel', hle'⟩
  exact ⟨t, before', after', hts, hst, hrest⟩
namespace KruskalTree
-- Measures the total structural size of a Kruskal tree for termination arguments.
mutual
def transComplexity {X : Type} : KruskalTree X → Nat
  | .base _ => 1
  | .node ts => transComplexityList ts + 1
-- Measures the total structural size of a list of Kruskal trees.
def transComplexityList {X : Type} : List (KruskalTree X) → Nat
  | [] => 0
  | t :: ts => transComplexity t + transComplexityList ts
end
-- The complexity of a concatenated forest is the sum of the complexities of its two parts.
@[simp]
theorem transComplexityList_append {X : Type} (before after : List (KruskalTree X)) :
        transComplexityList (before ++ after) = transComplexityList before +
            transComplexityList after := by
  induction before with
  | nil => simp [transComplexityList]
  | cons t before ih => simp [transComplexityList, ih, Nat.add_assoc]

-- Every Kruskal tree has strictly positive structural complexity.
theorem transComplexity_pos {X : Type} (t : KruskalTree X) :
        0 < transComplexity t := by
  cases t with
  | base x => simp [transComplexity]
  | node ts => simp [transComplexity]
-- Transitivity
mutual
-- Kruskal tree embedding is transitive whenever the underlying relation is transitive.
theorem KruskalTreeEmbeds_trans {X : Type} {r : X → X → Prop} [IsPreorder X r]
        {a b c : KruskalTree X} (hab : KruskalTreeEmbeds r a b)
        (hbc : KruskalTreeEmbeds r b c) :
        KruskalTreeEmbeds r a c := by
  cases hbc with
  | base hbcBase =>
      cases hab with
      | base habBase =>
          exact KruskalTreeEmbeds.base (IsTrans.trans _ _ _ habBase hbcBase)
  | root hbcForest =>
      cases hab with
      | root habForest =>
          exact KruskalTreeEmbeds.root (KruskalForestEmbeds_trans
              habForest hbcForest)
      | @descend a b₀ before after habSub =>
          obtain ⟨u, before', after', hc, hb₀u, _⟩ :=
            KruskalForestEmbeds_extract (before := before) (after := after)
              (s := b₀) hbcForest
          rw [hc]; apply KruskalTreeEmbeds.descend
          exact KruskalTreeEmbeds_trans habSub hb₀u
  | @descend b c₀ before after hbcSub =>
      apply KruskalTreeEmbeds.descend
      exact KruskalTreeEmbeds_trans hab hbcSub
termination_by KruskalTree.transComplexity a + KruskalTree.transComplexity b +
  KruskalTree.transComplexity c
decreasing_by
  all_goals
    subst_vars
    simp [KruskalTree.transComplexity, KruskalTree.transComplexityList,
      KruskalTree.transComplexityList_append]
    omega
-- Kruskal forest embedding is transitive whenever the underlying tree embedding is transitive.
theorem KruskalForestEmbeds_trans {X : Type} {r : X → X → Prop} [IsPreorder X r]
        {as bs cs : List (KruskalTree X)} (hab : KruskalForestEmbeds r as bs)
        (hbc : KruskalForestEmbeds r bs cs) :
        KruskalForestEmbeds r as cs := by
  cases hab with
  | nil => exact KruskalForestEmbeds.nil
  | @cons a b as before after habTree habRest =>
      obtain ⟨c, before', after', hcs, hbcTree, hbcRest⟩ :=
        KruskalForestEmbeds_extract (before := before) (after := after)
          (s := b) hbc
      rw [hcs]
      exact KruskalForestEmbeds.cons (KruskalTreeEmbeds_trans habTree hbcTree)
        (KruskalForestEmbeds_trans habRest hbcRest)
termination_by
  KruskalTree.transComplexityList as +
  KruskalTree.transComplexityList bs +
  KruskalTree.transComplexityList cs + 1
decreasing_by
  all_goals
    subst_vars
    try have haPos : 0 < KruskalTree.transComplexity a :=
        KruskalTree.transComplexity_pos a
    try have hbPos : 0 < KruskalTree.transComplexity b :=
        KruskalTree.transComplexity_pos b
    try have hcPos : 0 < KruskalTree.transComplexity c :=
        KruskalTree.transComplexity_pos c
    simp [KruskalTree.transComplexity, KruskalTree.transComplexityList,
      KruskalTree.transComplexityList_append]
    omega
end
-- Kruskal tree embedding is a preorder whenever the underlying relation is a preorder.s
instance KruskalTreeEmbeds_isPreorder {X : Type} {r : X → X → Prop}
        [IsPreorder X r] : IsPreorder (KruskalTree X) (KruskalTreeEmbeds r) where
  refl := by intro t; exact KruskalTreeEmbeds_refl t
  trans := by intro a b c hab hbc; exact KruskalTreeEmbeds_trans hab hbc
-- Bad Sequence argument
-- A Kruskal bad sequence is an infinite sequence with no earlier tree embedding into a later tree.
abbrev KruskalBadSeq {X : Type} (r : X → X → Prop)
        (f : ℕ → KruskalTree X) : Prop :=
  Set.PartiallyWellOrderedOn.IsBadSeq (KruskalTreeEmbeds r) Set.univ f
-- A Kruskal minimal bad sequence is bad and cannot be made bad by replacing position
-- n by a smaller tree.
abbrev KruskalMinBadSeq {X : Type} (r : X → X → Prop) (n : ℕ) (f : ℕ → KruskalTree X) : Prop :=
  Set.PartiallyWellOrderedOn.IsMinBadSeq (KruskalTreeEmbeds r)  KruskalTree.transComplexity
    Set.univ n f
-- If any bad Kruskal sequence exists, then there exists one which is complexity-minimal
-- at every position.
theorem exists_KruskalMinBadSeq {X : Type} {r : X → X → Prop}
        (hbad : ∃ f : ℕ → KruskalTree X, KruskalBadSeq r f) :
  ∃ f : ℕ → KruskalTree X, KruskalBadSeq r f ∧ ∀ n, KruskalMinBadSeq r n f := by
  exact Set.PartiallyWellOrderedOn.exists_min_bad_of_exists_bad
      (KruskalTreeEmbeds r) KruskalTree.transComplexity Set.univ hbad
-- Partiall Well Ordered
-- Base
def KruskalBaseSet {X : Type} : Set (KruskalTree X) := {t | ∃ x : X, t = .base x}
/- If the underlying labels are WQO, then the corresponding base trees are WQO under
   Kruskal embedding.-/
theorem KruskalBaseSet_partiallyWellOrderedOn {X : Type} {r : X → X → Prop}
        (hX : WellQuasiOrdered r) :
        (KruskalBaseSet (X := X)).PartiallyWellOrderedOn (KruskalTreeEmbeds r) := by
  rw [Set.partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  have hfBase : ∀ n, ∃ x : X, f n = (.base x : KruskalTree X) := by intro n; exact hf n
  choose g hg using hfBase; obtain ⟨i, j, hij, hgij⟩ := hX g
  refine ⟨i, j, hij, ?_⟩; rw [hg i, hg j]
  exact KruskalTreeEmbeds.base hgij
/- In a bad Kruskal sequence over WQO labels, all sufficiently late terms must be node trees
   rather than bases. -/
theorem KruskalBadSeq_eventually_node {X : Type} {r : X → X → Prop} (hX : WellQuasiOrdered r)
        {f : ℕ → KruskalTree X} (hbad : KruskalBadSeq r f) :
        ∃ k, ∀ n, k < n → ∃ ts, f n = .node ts := by
  have hBase : (KruskalBaseSet (X := X)).PartiallyWellOrderedOn (KruskalTreeEmbeds r) :=
    KruskalBaseSet_partiallyWellOrderedOn hX
  obtain ⟨k, hk⟩ := hBase.exists_notMem_of_gt hbad.2; refine ⟨k, ?_⟩
  intro n hkn
  have hnotBase : f n ∉ KruskalBaseSet (X := X) := hk n hkn
  cases hfn : f n with
  | base x => exfalso; apply hnotBase; exact ⟨x, hfn⟩
  | node ts => exact ⟨ts, rfl⟩
-- Every immediate child of a node has strictly smaller complexity than the whole node.
theorem transComplexity_lt_node_of_mem {X : Type} {t : KruskalTree X}
        {ts : List (KruskalTree X)} (ht : t ∈ ts) :
        transComplexity t < transComplexity (.node ts) := by
  induction ts with
  | nil => simp at ht
  | cons u us ih =>
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · simp only [transComplexity, transComplexityList]; omega
      · have htu : transComplexity t < transComplexity (.node us) := ih ht
        have huPos : 0 < transComplexity u := transComplexity_pos u
        simp only [transComplexity, transComplexityList] at htu ⊢
        omega
-- Every immediate child of a Kruskal node embeds into the whole node.
theorem KruskalTreeEmbeds_child {X : Type} {r : X → X → Prop} [IsPreorder X r]
        {t : KruskalTree X} {ts : List (KruskalTree X)} (ht : t ∈ ts) :
        KruskalTreeEmbeds r t (.node ts) := by
  obtain ⟨before, after, hts⟩ := List.append_of_mem ht
  rw [hts]; apply KruskalTreeEmbeds.descend
  exact KruskalTreeEmbeds_refl t
-- Minimality says replacing f n by one of its strictly smaller children cannot still
-- produce a bad sequence.
theorem KruskalMinBadSeq_no_child_bad {X : Type} {r : X → X → Prop}
        {f g : ℕ → KruskalTree X} {n : ℕ} {ts : List (KruskalTree X)}
        {t : KruskalTree X} (hmin : KruskalMinBadSeq r n f) (hfn : f n = .node ts)
        (ht : t ∈ ts) (hprefix : ∀ m < n, f m = g m) (hgn : g n = t) :
        ¬ KruskalBadSeq r g := by
  have hsmall : KruskalTree.transComplexity (g n) < KruskalTree.transComplexity (f n) := by
    rw [hgn, hfn]; exact KruskalTree.transComplexity_lt_node_of_mem ht
  exact hmin g hprefix hsmall
-- KruskalForestOn S ts means that every tree occurring in the forest ts belongs to S.
def KruskalForestOn {X : Type}
        (S : Set (KruskalTree X))
        (ts : List (KruskalTree X)) : Prop :=
  ∀ t, t ∈ ts → t ∈ S
-- Higman's ordered list embedding implies our unordered Kruskal forest embedding.
theorem KruskalForestEmbeds_of_sublistForall₂ {X : Type} {r : X → X → Prop}
        {ss ts : List (KruskalTree X)} (h : List.SublistForall₂ (KruskalTreeEmbeds r) ss ts) :
        KruskalForestEmbeds r ss ts := by
  induction h with
  | nil => exact KruskalForestEmbeds.nil
  | cons hst hrest ih =>
      simpa using (KruskalForestEmbeds.cons (before := []) hst ih)
  | @cons_right t ss ts hrest ih =>
      exact KruskalForestEmbeds_weaken_cons ih t
-- If a set of Kruskal trees is WQO, then finite forests made from that set are WQO.
theorem KruskalForestEmbeds_partiallyWellOrderedOn {X : Type} {r : X → X → Prop}
        [IsPreorder X r] {S : Set (KruskalTree X)}
        (hS : S.PartiallyWellOrderedOn (KruskalTreeEmbeds r)) :
        {ts : List (KruskalTree X) | KruskalForestOn S ts}.PartiallyWellOrderedOn
            (KruskalForestEmbeds r) := by
  have hHigman := Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂
      (KruskalTreeEmbeds r) hS
  rw [Set.partiallyWellOrderedOn_iff_exists_lt]
    at hHigman ⊢
  intro f hf
  obtain ⟨i, j, hij, hsub⟩ := hHigman f hf
  exact ⟨i, j, hij, KruskalForestEmbeds_of_sublistForall₂ hsub⟩
end KruskalTree
namespace GapTree
-- Children of a Minimal Bad Kruskal Sequence
-- KruskalChildrenOfSeq f is the set of all immediate children occurring in trees of the sequence f.
def KruskalChildrenOfSeq {X : Type}
        (f : ℕ → KruskalTree X) :
        Set (KruskalTree X) :=
  {t | ∃ n ts, f n = .node ts ∧ t ∈ ts}
-- The immediate children occurring in a globally minimal bad sequence form a WQO set.
theorem KruskalChildrenOfMinBad_partiallyWellOrderedOn
        {X : Type} {r : X → X → Prop}
        [IsPreorder X r] {f : ℕ → KruskalTree X}
        (hbad : KruskalTree.KruskalBadSeq r f)
        (hmin : ∀ n, KruskalTree.KruskalMinBadSeq r n f) :
        (KruskalChildrenOfSeq f).PartiallyWellOrderedOn
          (KruskalTreeEmbeds r) := by
  classical
  rw [Set.PartiallyWellOrderedOn.iff_forall_not_isBadSeq]
  intro R hR
  -- Every R(n) occurs as a child of some f(p(n)).
  have hFamily : ∀ n, ∃ p ts, f p = .node ts ∧ R n ∈ ts := by
    intro n; exact hR.1 n
  choose p ts hpNode hpMem using hFamily
  have hex : ∃ k : ℕ, ∃ n : ℕ, p n = k := ⟨p 0, 0, rfl⟩
  let k : ℕ := Nat.find hex
  have hkSpec : ∃ n : ℕ, p n = k := by
    simpa [k] using Nat.find_spec hex
  obtain ⟨l, hpl⟩ := hkSpec
  let g : ℕ → KruskalTree X := fun n => R (l + n)
  let h : ℕ → ℕ := fun n => p (l + n)
  have hgBad : KruskalTree.KruskalBadSeq r g := by
    constructor
    · intro n; simp
    · intro m n hmn hEmbed
      apply hR.2 (l + m) (l + n)
      · omega
      · simpa [g] using hEmbed
  have hkLe : ∀ q : ℕ, k ≤ p q := by
    intro q
    dsimp [k]
    exact Nat.find_min' hex ⟨q, rfl⟩
  have hh : ∀ n, h 0 ≤ h n := by
    intro n
    have hk : k ≤ p (l + n) := hkLe (l + n)
    have hh0 : h 0 = k := by simp [h, hpl]
    rw [hh0]
    simpa [h] using hk
  have hgNode : ∀ n, f (h n) = .node (ts (l + n)) := by
    intro n
    simpa [h] using hpNode (l + n)
  have hgMem : ∀ n, g n ∈ ts (l + n) := by
    intro n
    simpa [g] using hpMem (l + n)
  have hgEmbedParent : ∀ n, KruskalTreeEmbeds r (g n) (f (h n)) := by
    intro n
    rw [hgNode n]
    exact KruskalTree.KruskalTreeEmbeds_child (hgMem n)
  let comb : ℕ → KruskalTree X := fun n =>
    if n < h 0 then f n else g (n - h 0)
  have hcombBad : KruskalTree.KruskalBadSeq r comb := by
    constructor
    · intro n; simp
    · intro m n hmn hEmbed
      by_cases hn : n < h 0
      · have hm : m < h 0 := hmn.trans hn
        have hEmbed' : KruskalTreeEmbeds r (f m) (f n) := by
          simpa [comb, hm, hn] using hEmbed
        exact hbad.2 m n hmn hEmbed'
      · have hnge : h 0 ≤ n := Nat.le_of_not_gt hn
        by_cases hm : m < h 0
        · have hEmbed' : KruskalTreeEmbeds r (f m) (g (n - h 0)) := by
            simpa [comb, hm, hn] using hEmbed
          have hIntoParent :
              KruskalTreeEmbeds r (g (n - h 0)) (f (h (n - h 0))) :=
            hgEmbedParent (n - h 0)
          have hWhole :
              KruskalTreeEmbeds r (f m) (f (h (n - h 0))) :=
            KruskalTree.KruskalTreeEmbeds_trans hEmbed' hIntoParent
          have hmParent : m < h (n - h 0) :=
            lt_of_lt_of_le hm (hh (n - h 0))
          exact hbad.2 m (h (n - h 0)) hmParent hWhole
        · have hmge : h 0 ≤ m := Nat.le_of_not_gt hm
          have hsub : m - h 0 < n - h 0 := by omega
          have hEmbed' : KruskalTreeEmbeds r (g (m - h 0)) (g (n - h 0)) := by
            simpa [comb, hm, hn] using hEmbed
          exact hgBad.2 (m - h 0) (n - h 0) hsub hEmbed'
  have hprefix : ∀ m < h 0, f m = comb m := by
    intro m hm
    simp [comb, hm]
  have hcombAt : comb (h 0) = g 0 := by simp [comb]
  have hnotBad : ¬ KruskalTree.KruskalBadSeq r comb :=
    KruskalTree.KruskalMinBadSeq_no_child_bad
      (hmin (h 0)) (hgNode 0) (hgMem 0) hprefix hcombAt
  exact hnotBad hcombBad


--=================================================================================================
-- Kruskal's Tree Theorem
--=================================================================================================
-- If the base relation is WQO, then finite Kruskal trees are WQO under homeomorphic embedding.
theorem KruskalTreeEmbeds_wqo
        {X : Type} {r : X → X → Prop}
        [IsPreorder X r] (hX : WellQuasiOrdered r) :
        WellQuasiOrdered (KruskalTreeEmbeds r) := by
  classical
  rw [← Set.partiallyWellOrderedOn_univ_iff]
  rw [Set.PartiallyWellOrderedOn.iff_not_exists_isMinBadSeq
    KruskalTree.transComplexity]
  rintro ⟨f, hbad, hmin⟩
  have hChildren :
      (KruskalChildrenOfSeq f).PartiallyWellOrderedOn
        (KruskalTreeEmbeds r) :=
    KruskalChildrenOfMinBad_partiallyWellOrderedOn hbad hmin
  obtain ⟨k, hkNode⟩ :=
    KruskalTree.KruskalBadSeq_eventually_node hX hbad
  have hNodeTail : ∀ n, ∃ ts, f (k + 1 + n) = .node ts := by
    intro n
    apply hkNode
    omega
  choose forests hForests using hNodeTail
  have hForestOn :
      ∀ n, KruskalTree.KruskalForestOn (KruskalChildrenOfSeq f) (forests n) := by
    intro n t ht
    exact ⟨k + 1 + n, forests n, hForests n, ht⟩
  have hForestWQO :
      {ts : List (KruskalTree X) |
        KruskalTree.KruskalForestOn (KruskalChildrenOfSeq f) ts}.PartiallyWellOrderedOn
          (KruskalForestEmbeds r) :=
    KruskalTree.KruskalForestEmbeds_partiallyWellOrderedOn hChildren
  rw [Set.partiallyWellOrderedOn_iff_exists_lt] at hForestWQO
  obtain ⟨i, j, hij, hForestEmbed⟩ :=
    hForestWQO forests hForestOn
  have hTreeEmbed :
      KruskalTreeEmbeds r (f (k + 1 + i)) (f (k + 1 + j)) := by
    rw [hForests i, hForests j]
    exact KruskalTreeEmbeds.root hForestEmbed
  have hIndices : k + 1 + i < k + 1 + j := by omega
  exact hbad.2 (k + 1 + i) (k + 1 + j) hIndices hTreeEmbed
end GapTree
/- Outline
   1. Build the two layer Kruskal strucutre like the gaptree label 0 and 1
   2. Encode GapTree into the iterated Kruskal structure
   3. prove order preservation
   4. apply wqo of Kruskal to conclude GapTreeEmbeds_wqo -/
--=====================================================================================
-- T_n(X) notation of Freund
/- T_n(X) is the system of finite trees with n possible/available internal labels where X supplies
   the optional objects that can occer at the leaves. Freund proves T_n(0) corresponds to tree
   labelled 0, ..., n-1 with the strong gap embedding.
   T₀(X) = X
   T₁(X) ≃ KruskalTree X
    for example, .node [.base x .node [.base y]] can be pictured with only available node 0
          0
         / \
       [x]  0
            |
           [y]
   T₂(X) has two possible nodes 0 or 1. T₂^{-}(X) is thought as the new layer to add on T₁(X).
   This shifts the old 0 to 1 and a new node 0 is introduced.  -/
namespace GapTree
/- As explained above the nodes are pushed up from T₁ to T₂. So,
   Kruskal2Minus.node represents a new label-0 node
   KruskalTree.node represents a label-1 node      -/
inductive Kruskal2Minus where
  | node : List (KruskalTree Kruskal2Minus) → Kruskal2Minus
-- T₂ is an ordinary Kruskal layer built over T₂^{-}
abbrev Kruskal2 := KruskalTree Kruskal2Minus
/- A Kruskal2Minus object appears inside Kruskal2 as a base.
    For example
              node
              |
              node
              |
            base u
    represents
              1
              |
              1
              |
              0
    where the bottom 0-node is the Kruskal2Minus object u. -/
-- The base label x occers somewhere inside the Kruskal tree t
inductive KruskalBaseOccurs {X : Type} (x : X) : KruskalTree X → Prop where
  | base : KruskalBaseOccurs x (.base x)
  | node {t : KruskalTree X} {ts : List (KruskalTree X)} (ht : t ∈ ts) (h : KruskalBaseOccurs x t) :
    KruskalBaseOccurs x (.node ts)
-- x occus inside at least one tree of the forest
def KruskalBaseOccursForest (x : X) (ts : List (KruskalTree X)) : Prop :=
  ∃ t, t ∈ ts ∧ KruskalBaseOccurs x t
-- If x occurs inside a member of a forest, then x occurs inside the whole forest
theorem KruskalBaseOccursForest_of_mem {X : Type} {x : X} {t : KruskalTree X}
        {ts : List (KruskalTree X)} (ht : t ∈ ts) (hx : KruskalBaseOccurs x t) :
        KruskalBaseOccursForest x ts := by
  exact ⟨t, ht, hx⟩
-- A base label occurs in the one-node Kruskal tree containing exactly that base.
theorem KruskalBaseOccurs_base {X : Type} (x : X) : KruskalBaseOccurs x (.base x : KruskalTree X) :=
  by exact KruskalBaseOccurs.base
-- Occurrence propagates upward when the containing tree is made a child of a new Kruskal node
theorem KruskalBaseOccurs_node {X : Type} {x : X} {t : KruskalTree X} {ts : List (KruskalTree X)}
        (ht : t ∈ ts) (hx : KruskalBaseOccurs x t) :
        KruskalBaseOccurs x (.node ts) := by
  exact KruskalBaseOccurs.node ht hx
-- A base label occurring in a tree of a forest also occurs after unused trees are added before it.
theorem KruskalBaseOccursForest_of_append_left {X : Type} {x : X} {ts : List (KruskalTree X)}
        (before : List (KruskalTree X)) (h : KruskalBaseOccursForest x ts) :
        KruskalBaseOccursForest x (before ++ ts) := by
  obtain ⟨t, ht, hx⟩ := h; refine ⟨t, ?_, hx⟩; simp [ht]
-- A base label occurring in a tree of a forest also occurs after unused trees are added after it.
theorem KruskalBaseOccursForest_of_append_right {X : Type} {x : X} {ts : List (KruskalTree X)}
        (after : List (KruskalTree X)) (h : KruskalBaseOccursForest x ts) :
        KruskalBaseOccursForest x (ts ++ after) := by
  obtain ⟨t, ht, hx⟩ := h; refine ⟨t, ?_, hx⟩; simp [ht]
--================================================================================================
-- Two-label Kruskal Embedding
/- For two label-0 objects s and t,
   root : compare their child forests
   descend : s can embed into a label-0 object u occuring inside one of t's children (the process
             is to find the "base" so only crosses label-1's on its way to u.)
    root:

      0                         0
    / | \                     / | \
   s₁ s₂ ...      embeds      t₁ t₂ ...


    descend:

                0
                |
                1
                |
                1
                |
                0  ← u

s embeds u
s embeds whole tree -/
inductive Kruskal2MinusEmbeds : Kruskal2Minus → Kruskal2Minus → Prop where
  | root {ss ts : List (KruskalTree Kruskal2Minus)}
         (h : KruskalForestEmbeds Kruskal2MinusEmbeds ss ts) :
    Kruskal2MinusEmbeds (.node ss) (.node ts)
  | descend {s u : Kruskal2Minus} {ts : List (KruskalTree Kruskal2Minus)}
            (hu : KruskalBaseOccursForest u ts) (h : Kruskal2MinusEmbeds s u) :
    Kruskal2MinusEmbeds s (.node ts)
abbrev Kruskal2Embeds : Kruskal2 → Kruskal2 → Prop := KruskalTreeEmbeds Kruskal2MinusEmbeds
abbrev Kruskal2ForestEmbeds : List Kruskal2 → List Kruskal2 → Prop :=
  KruskalForestEmbeds Kruskal2MinusEmbeds
-- Reflexivity (Embedding to itself)
mutual
-- Simply every label-0 two lebel Kruskal object embeds into itself
theorem Kruskal2MinusEmbeds_refl (s : Kruskal2Minus) : Kruskal2MinusEmbeds s s := by
  cases s with
  | node ss => apply Kruskal2MinusEmbeds.root
               exact Kruskal2ForestEmbeds_refl ss
-- Every 2-level Kruskal tree embeds into itself
theorem Kruskal2Embeds_refl (s : Kruskal2) : Kruskal2Embeds s s := by
  cases s with
  | base x => exact KruskalTreeEmbeds.base (Kruskal2MinusEmbeds_refl x)
  | node ss => apply KruskalTreeEmbeds.root
               exact Kruskal2ForestEmbeds_refl ss
-- Every two level Kruskal forest emebds into itself
theorem Kruskal2ForestEmbeds_refl (ss : List Kruskal2) :
        Kruskal2ForestEmbeds ss ss := by
  cases ss with
  | nil => exact KruskalForestEmbeds.nil
  | cons s ss =>
      have hs : Kruskal2Embeds s s := Kruskal2Embeds_refl s
      have hss : Kruskal2ForestEmbeds ss ss :=
        Kruskal2ForestEmbeds_refl ss
      simpa using (KruskalForestEmbeds.cons (s := s) (t := s) (ss := ss)
          (before := []) (after := ss) hs hss)
end
/- We want some support-transport lemma that satisfies something like the following:
   x occurs in s and s ≤ t → ∃ y, y occurs in t and x ≤ y -/
mutual
/- Given a base object x occuring in s and s embeds into t, there is some base object y in t
   such that r x y -/
theorem KruskalBaseOccurs_of_embeds {X : Type} {r : X → X → Prop} {x : X} {s t : KruskalTree X}
        (hx : KruskalBaseOccurs x s) (h : KruskalTreeEmbeds r s t) :
        ∃ y, KruskalBaseOccurs y t ∧ r x y := by
  cases h with
  | base hxy => cases hx with
                | base => exact ⟨_, KruskalBaseOccurs.base, hxy⟩
  | @root ss ts hforest =>
    cases hx with
    | @node u ss hu hx => have hSource : KruskalBaseOccursForest x ss := by exact ⟨u, hu, hx⟩
                          obtain ⟨y, hyForest, hxy⟩ :=
                           KruskalBaseOccursForest_of_embeds hSource hforest
                          obtain ⟨v, hv, hyv⟩ := hyForest
                          refine ⟨y, ?_, hxy⟩
                          exact KruskalBaseOccurs.node hv hyv
  | @descend s u before after hsub =>
      obtain ⟨y, hy, hxy⟩ := KruskalBaseOccurs_of_embeds hx hsub
      refine ⟨y, ?_, hxy⟩
      apply KruskalBaseOccurs.node (t := u)
      · simp
      · exact hy
termination_by
  2 * (KruskalTree.transComplexity s + KruskalTree.transComplexity t)
decreasing_by
  all_goals subst_vars
  all_goals simp [KruskalTree.transComplexity, KruskalTree.transComplexityList,
    KruskalTree.transComplexityList_append]
  all_goals omega

/- An embedded forest carries every occurring base label to an embedding-related base label
   in the target forest. -/
theorem KruskalBaseOccursForest_of_embeds {X : Type} {r : X → X → Prop} {x : X}
        {ss ts : List (KruskalTree X)} (hx : KruskalBaseOccursForest x ss)
        (h : KruskalForestEmbeds r ss ts) :
        ∃ y, KruskalBaseOccursForest y ts ∧ r x y := by
 cases h with
  | nil => obtain ⟨u, hu, _⟩ := hx; simp at hu
  | @cons s t ss before after hst hrest =>
      obtain ⟨u, hu, hxu⟩ := hx
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      -- x occurs inside the source tree matched with t.
      · obtain ⟨y, hyt, hxy⟩ := KruskalBaseOccurs_of_embeds hxu hst
        refine ⟨y, ?_, hxy⟩; refine ⟨t, ?_, hyt⟩; simp
      -- x occurs in the remainder of the source forest.
      · have hxRest : KruskalBaseOccursForest x ss := by
          exact ⟨u, hu, hxu⟩
        obtain ⟨y, hyRest, hxy⟩ :=
          KruskalBaseOccursForest_of_embeds hxRest hrest
        obtain ⟨v, hv, hyv⟩ := hyRest
        refine ⟨y, ?_, hxy⟩; refine ⟨v, ?_, hyv⟩
        simp only [List.mem_append, List.mem_cons] at hv ⊢
        rcases hv with hv | hv
        · exact Or.inl hv
        · exact Or.inr (Or.inr hv)
termination_by
  2 * (KruskalTree.transComplexityList ss + KruskalTree.transComplexityList ts) + 1
decreasing_by
  all_goals subst_vars
  all_goals try have hsPos := KruskalTree.transComplexity_pos s
  all_goals try have htPos := KruskalTree.transComplexity_pos t
  all_goals simp [KruskalTree.transComplexity, KruskalTree.transComplexityList,
    KruskalTree.transComplexityList_append]
  all_goals omega
end
--========================================================================================
-- Two-Level Kruskal Structural Complexity
/- Unlike ordinary Kruskal complexity, this complexity also counts the
   Kruskal2Minus object hidden inside a base, so both labels 0 and 1
   contribute to the measure. -/
mutual
-- Measures the complete structural complexity of a label-0 Kruskal2Minus object.
def Kruskal2Minus_cmplx (s : Kruskal2Minus) : Nat :=
  match s with
  | .node ts => Kruskal2Forest_cmplx ts + 1
  termination_by sizeOf s
  decreasing_by all_goals simp_wf
-- Measures the complete structural complexity of a two-level Kruskal tree.
def Kruskal2_cmplx (t : Kruskal2) : Nat :=
  match t with
  | .base x => Kruskal2Minus_cmplx x + 1
  | .node ts => Kruskal2Forest_cmplx ts + 1
  termination_by sizeOf t
  decreasing_by all_goals simp_wf
-- Measures the total structural complexity of a forest of two-level Kruskal trees.
def Kruskal2Forest_cmplx (ts : List Kruskal2) : Nat :=
  match ts with
  | [] => 0
  | t :: ts => Kruskal2_cmplx t + Kruskal2Forest_cmplx ts + 1
  termination_by sizeOf ts
  decreasing_by all_goals simp_wf <;> omega
end
-- Arithmetics
-- The complexity of concatenated two-level forests is the sum of their complexities.
@[simp]
theorem Kruskal2Forest_cmplx_append (ss ts : List Kruskal2) :
        Kruskal2Forest_cmplx (ss ++ ts) = Kruskal2Forest_cmplx ss + Kruskal2Forest_cmplx ts := by
  induction ss with
  | nil => simp [Kruskal2Forest_cmplx]
  | cons s ss ih => simp [Kruskal2Forest_cmplx, ih]; omega
-- Every label-0 Kruskal2Minus object has positive complexity.
theorem Kruskal2Minus_cmplx_pos (s : Kruskal2Minus) :
        0 < Kruskal2Minus_cmplx s := by
  cases s with
  | node ss => simp [Kruskal2Minus_cmplx]
-- Every full two-level Kruskal tree has positive complexity.
theorem Kruskal2_cmplx_pos (t : Kruskal2) : 0 < Kruskal2_cmplx t := by
  cases t with
  | base x => simp [Kruskal2_cmplx]
  | node ts => simp [Kruskal2_cmplx]
-- Every tree occurring in a forest has smaller complexity than the whole forest.
theorem Kruskal2_cmplx_lt_forest_of_mem {t : Kruskal2} {ts : List Kruskal2}
        (ht : t ∈ ts) :
        Kruskal2_cmplx t < Kruskal2Forest_cmplx ts := by
  induction ts with
  | nil => simp at ht
  | cons u us ih =>
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · simp [Kruskal2Forest_cmplx]
      · have h := ih ht
        have huPos := Kruskal2_cmplx_pos u
        simp [Kruskal2Forest_cmplx] at h ⊢
        omega
-- A base object occurring inside a two-level tree is strictly smaller than the whole tree.
theorem Kruskal2Minus_cmplx_lt_of_occurs {x : Kruskal2Minus} {t : Kruskal2}
        (hx : KruskalBaseOccurs x t) :
        Kruskal2Minus_cmplx x < Kruskal2_cmplx t := by
  induction hx with
  | base => simp [Kruskal2_cmplx]
  | @node t ts ht hx ih =>
      have htSmall : Kruskal2_cmplx t < Kruskal2Forest_cmplx ts :=
        Kruskal2_cmplx_lt_forest_of_mem ht
      simp [Kruskal2_cmplx]
      omega
-- A base object occurring somewhere in a forest is smaller than the complete forest.
theorem Kruskal2Minus_cmplx_lt_forest_of_occurs {x : Kruskal2Minus}
        {ts : List Kruskal2} (hx : KruskalBaseOccursForest x ts) :
        Kruskal2Minus_cmplx x < Kruskal2Forest_cmplx ts := by
  obtain ⟨t, ht, hxt⟩ := hx
  have hxTree : Kruskal2Minus_cmplx x < Kruskal2_cmplx t :=
    Kruskal2Minus_cmplx_lt_of_occurs hxt
  have htForest : Kruskal2_cmplx t < Kruskal2Forest_cmplx ts :=
    Kruskal2_cmplx_lt_forest_of_mem ht
  omega
-- A supported label-0 object is strictly smaller than the label-0 node containing that support.
theorem Kruskal2Minus_cmplx_lt_node_of_occurs {x : Kruskal2Minus}
        {ts : List Kruskal2} (hx : KruskalBaseOccursForest x ts) :
        Kruskal2Minus_cmplx x < Kruskal2Minus_cmplx (.node ts) := by
  have h := Kruskal2Minus_cmplx_lt_forest_of_occurs hx
  simp [Kruskal2Minus_cmplx]
  omega
-- Transitivity
mutual
-- Embedding between label-0 Kruskal2Minus objects is transitive
theorem Kruskal2MinusEmbeds_trans {a b c : Kruskal2Minus} (hab : Kruskal2MinusEmbeds a b)
        (hbc : Kruskal2MinusEmbeds b c) :
        Kruskal2MinusEmbeds a c := by
  cases hbc with
  | @root bs cs hbcForest =>
    cases hab with
    | root habForest =>
      exact Kruskal2MinusEmbeds.root (Kruskal2ForestEmbeds_trans habForest hbcForest)
    | @descend a u bs hu habSub =>
      -- ∃v, KruskalBaseOccursForest v ts ∧ r u v
      obtain ⟨v, hv, huv⟩ := KruskalBaseOccursForest_of_embeds hu hbcForest
      have huSmall : Kruskal2Minus_cmplx u < Kruskal2Minus_cmplx (.node bs) :=
        Kruskal2Minus_cmplx_lt_node_of_occurs hu
      have hvSmall : Kruskal2Minus_cmplx v < Kruskal2Minus_cmplx (.node cs) :=
        Kruskal2Minus_cmplx_lt_node_of_occurs hv
      have hav : Kruskal2MinusEmbeds a v := Kruskal2MinusEmbeds_trans habSub huv
      exact Kruskal2MinusEmbeds.descend hv hav
  | @descend b u cs hu hbcSub =>
      have huSmall : Kruskal2Minus_cmplx u < Kruskal2Minus_cmplx (.node cs) :=
        Kruskal2Minus_cmplx_lt_node_of_occurs hu
      -- Recursively compose a ≤ b ≤ u.
      have hau : Kruskal2MinusEmbeds a u :=
        Kruskal2MinusEmbeds_trans hab hbcSub
      -- Then descend from a to u inside c.
      exact Kruskal2MinusEmbeds.descend hu hau
termination_by
  3 * (Kruskal2Minus_cmplx a + Kruskal2Minus_cmplx b + Kruskal2Minus_cmplx c) + 2
decreasing_by
  all_goals
    subst_vars
    try simp [Kruskal2Minus_cmplx] at huSmall
    try simp [Kruskal2Minus_cmplx] at hvSmall
    simp [Kruskal2Minus_cmplx]
    omega
-- Embedding between complete two-level Kruskal trees is transitive
theorem Kruskal2Embeds_trans {a b c : Kruskal2} (hab : Kruskal2Embeds a b)
        (hbc : Kruskal2Embeds b c) : Kruskal2Embeds a c := by
  cases hbc with
  -- Both b and c are base objects, hence label-0 structures.
  | base hbcBase =>
      cases hab with
      | base habBase =>
          exact KruskalTreeEmbeds.base (Kruskal2MinusEmbeds_trans habBase hbcBase)
  -- b and c are ordinary outer Kruskal nodes, hence label-1 nodes.
  | @root bs cs hbcForest =>
      cases hab with
      -- a and b have matching label-1 roots.
      | root habForest =>
          exact KruskalTreeEmbeds.root (Kruskal2ForestEmbeds_trans habForest hbcForest)
      -- a embeds into one particular child b₀ of b.
      | @descend a b₀ before after habSub =>
          obtain ⟨c₀, before', after', hcs, hb₀c₀, _⟩ :=
            KruskalForestEmbeds_extract (before := before) (after := after)
              (s := b₀) hbcForest
          have hb₀Mem : b₀ ∈ before ++ b₀ :: after := by simp
          have hb₀Small : Kruskal2_cmplx b₀ < Kruskal2_cmplx (.node (before ++ b₀ :: after)) := by
            have h : Kruskal2_cmplx b₀ < Kruskal2Forest_cmplx (before ++ b₀ :: after) :=
              Kruskal2_cmplx_lt_forest_of_mem hb₀Mem
            simp only [Kruskal2_cmplx]
            exact h.trans (Nat.lt_succ_self _)
          have hc₀Small : Kruskal2_cmplx c₀ < Kruskal2_cmplx (.node cs) := by
            have hc₀Mem : c₀ ∈ cs := by rw [hcs]; simp
            have h : Kruskal2_cmplx c₀ < Kruskal2Forest_cmplx cs :=
              Kruskal2_cmplx_lt_forest_of_mem hc₀Mem
            simp only [Kruskal2_cmplx]
            exact h.trans (Nat.lt_succ_self _)
          rw [hcs]; apply KruskalTreeEmbeds.descend
          exact Kruskal2Embeds_trans habSub hb₀c₀
  -- b embeds into a child c₀ of the final label-1 node c.
  | @descend b c₀ before after hbcSub =>
      have hc₀Mem : c₀ ∈ before ++ c₀ :: after := by simp
      have hc₀Small : Kruskal2_cmplx c₀ < Kruskal2_cmplx (.node (before ++ c₀ :: after)) := by
        have h : Kruskal2_cmplx c₀ < Kruskal2Forest_cmplx (before ++ c₀ :: after) :=
          Kruskal2_cmplx_lt_forest_of_mem hc₀Mem
        simp only [Kruskal2_cmplx]
        exact h.trans (Nat.lt_succ_self _)
      apply KruskalTreeEmbeds.descend
      exact Kruskal2Embeds_trans
        hab
        hbcSub
termination_by
  3 * (Kruskal2_cmplx a + Kruskal2_cmplx b + Kruskal2_cmplx c) + 1
decreasing_by
  all_goals
    subst_vars
    try simp [Kruskal2_cmplx] at hb₀Small
    try simp [Kruskal2_cmplx] at hc₀Small
    simp [Kruskal2_cmplx]
    omega
-- Embedding between finite forest of two-level Kruskal trees is transitive
theorem Kruskal2ForestEmbeds_trans {as bs cs : List Kruskal2} (hab : Kruskal2ForestEmbeds as bs)
        (hbc : Kruskal2ForestEmbeds bs cs) : Kruskal2ForestEmbeds as cs := by
  cases hab with
  | nil => exact KruskalForestEmbeds.nil
  | @cons a b as before after habTree habRest =>
      obtain ⟨c, before', after', hcs, hbcTree, hbcRest⟩ :=
        KruskalForestEmbeds_extract (before := before) (after := after) (s := b) hbc
      have haPos : 0 < Kruskal2_cmplx a := Kruskal2_cmplx_pos a
      have hbPos : 0 < Kruskal2_cmplx b := Kruskal2_cmplx_pos b
      have hcPos : 0 < Kruskal2_cmplx c := Kruskal2_cmplx_pos c
      rw [hcs]
      exact KruskalForestEmbeds.cons
        (Kruskal2Embeds_trans habTree hbcTree)
        (Kruskal2ForestEmbeds_trans habRest hbcRest)
termination_by
  3 * (Kruskal2Forest_cmplx as + Kruskal2Forest_cmplx bs + Kruskal2Forest_cmplx cs)
decreasing_by
  all_goals
    subst_vars
    simp only [Kruskal2Forest_cmplx, Kruskal2Forest_cmplx_append]
    omega
end
/- Next steps
    1. Show Kruskal2MinusEmbeds is WQO (similar to KruskalTreeEmbeds so telling Codex to simulate)
    2. Get WQO of the full two level Kruskal trees
    3. Encode each GapTree as Kruskal2
    4. Prove Kruskal2 embedding reflets to a strong-gap
    5. Prove the actual strong-gap WQO
    Finish -/

-- Kruskal2Minus embedding is a preorder.
instance Kruskal2MinusEmbeds_isPreorder : IsPreorder Kruskal2Minus Kruskal2MinusEmbeds where
  refl := by intro s; exact Kruskal2MinusEmbeds_refl s
  trans := by intro a b c hab hbc; exact Kruskal2MinusEmbeds_trans hab hbc
-- Minimal Bad Sequences for T₂^{-}
-- A bad sequence of label-0 two-level Kruskal objects has no increasing pair.
abbrev Kruskal2MinusBadSeq (f : ℕ → Kruskal2Minus) : Prop :=
  Set.PartiallyWellOrderedOn.IsBadSeq Kruskal2MinusEmbeds Set.univ f
-- A minimal bad sequence is complexity-minimal at the indicated position.
abbrev Kruskal2MinusMinBadSeq (n : ℕ) (f : ℕ → Kruskal2Minus) : Prop :=
  Set.PartiallyWellOrderedOn.IsMinBadSeq Kruskal2MinusEmbeds Kruskal2Minus_cmplx Set.univ n f
-- Every bad T₂⁻ sequence admits a globally complexity-minimal bad sequence.
theorem exists_Kruskal2MinusMinBadSeq (hbad : ∃ f : ℕ → Kruskal2Minus, Kruskal2MinusBadSeq f) :
        ∃ f : ℕ → Kruskal2Minus, Kruskal2MinusBadSeq f ∧
          ∀ n, Kruskal2MinusMinBadSeq n f := by
  exact Set.PartiallyWellOrderedOn.exists_min_bad_of_exists_bad
      Kruskal2MinusEmbeds Kruskal2Minus_cmplx Set.univ hbad
-- The set of all T₂ child trees occurring in a sequence of T₂⁻ objects.
def Kruskal2ChildrenOfSeq (f : ℕ → Kruskal2Minus) : Set Kruskal2 :=
  {t | ∃ n ts, f n = .node ts ∧ t ∈ ts}

-- Supports of a Minimal Bad T₂^{-} Sequence
/- The support of a T₂⁻ sequence consists of every label-0 object occurring
   as a base somewhere inside one of the immediate T₂ children. -/
-- Kruskal2SupportOfSeq f is the set of all label-0 base objects occurring inside children of f.
def Kruskal2SupportOfSeq (f : ℕ → Kruskal2Minus) : Set Kruskal2Minus :=
  {x | ∃ n ts, f n = .node ts ∧ KruskalBaseOccursForest x ts}
-- Every support object of a parent is strictly smaller than that parent.
theorem Kruskal2SupportOfSeq_cmplx_lt {f : ℕ → Kruskal2Minus} {x : Kruskal2Minus}
        {n : ℕ} {ts : List Kruskal2} (hfn : f n = .node ts)
        (hx : KruskalBaseOccursForest x ts) :
        Kruskal2Minus_cmplx x < Kruskal2Minus_cmplx (f n) := by
  rw [hfn]; exact Kruskal2Minus_cmplx_lt_node_of_occurs hx
-- Every support object embeds into the label-0 parent in which it occurs.
theorem Kruskal2SupportOfSeq_embeds_parent {x : Kruskal2Minus} {ts : List Kruskal2}
        (hx : KruskalBaseOccursForest x ts) :
        Kruskal2MinusEmbeds x (.node ts) := by
  apply Kruskal2MinusEmbeds.descend hx; exact Kruskal2MinusEmbeds_refl x
-- The support objects occurring in a globally minimal bad T₂⁻ sequence form a WQO set.
theorem Kruskal2SupportOfMinBad_partiallyWellOrderedOn {f : ℕ → Kruskal2Minus}
        (hbad : Kruskal2MinusBadSeq f) (hmin : ∀ n, Kruskal2MinusMinBadSeq n f) :
        (Kruskal2SupportOfSeq f).PartiallyWellOrderedOn Kruskal2MinusEmbeds := by
  classical
  rw [Set.PartiallyWellOrderedOn.iff_forall_not_isBadSeq]
  intro R hR
  -- Every R(n) is a support object of some parent f(p(n)).
  have hFamily : ∀ n, ∃ p ts, f p = .node ts ∧ KruskalBaseOccursForest (R n) ts := by
    intro n; simpa [Kruskal2SupportOfSeq] using hR.1 n
  choose p ts hpNode hpOccurs using hFamily
  -- Pick the least parent index containing some member of R.
  have hex : ∃ k : ℕ, ∃ n : ℕ, p n = k := by exact ⟨p 0, 0, rfl⟩
  let k : ℕ := Nat.find hex
  have hkSpec : ∃ n : ℕ, p n = k := by
    simpa [k] using Nat.find_spec hex
  obtain ⟨l, hpl⟩ := hkSpec
  -- Take the tail of R beginning at an occurrence with least parent index.
  let g : ℕ → Kruskal2Minus := fun n => R (l + n)
  let h : ℕ → ℕ := fun n => p (l + n)
  -- A tail of a bad sequence is still bad.
  have hgBad : Kruskal2MinusBadSeq g := by
    constructor
    · intro n; simp
    · intro m n hmn hEmbed
      apply hR.2 (l + m) (l + n)
      · omega
      · simpa [g] using hEmbed
  -- k is below every parent index selected by p.
  have hkLe : ∀ q : ℕ, k ≤ p q := by
    intro q; dsimp [k]
    exact Nat.find_min' hex ⟨q, rfl⟩
  -- Therefore h(0) is below every later selected parent index.
  have hh : ∀ n, h 0 ≤ h n := by
    intro n
    have hk : k ≤ p (l + n) := hkLe (l + n)
    have hh0 : h 0 = k := by simp [h, hpl]
    rw [hh0]; simpa [h] using hk
  -- g(n) occurs inside the child forest of its corresponding parent.
  have hgNode : ∀ n, f (h n) = .node (ts (l + n)) := by
    intro n; simpa [h] using hpNode (l + n)
  have hgOccurs : ∀ n, KruskalBaseOccursForest (g n) (ts (l + n)) := by
    intro n; simpa [g] using hpOccurs (l + n)
  -- Hence every g(n) embeds into the parent f(h(n)).
  have hgEmbedParent : ∀ n, Kruskal2MinusEmbeds (g n) (f (h n)) := by
    intro n; rw [hgNode n]
    exact Kruskal2SupportOfSeq_embeds_parent (hgOccurs n)
  -- Replace f(h 0) and everything afterwards by the bad support sequence g.
  let comb : ℕ → Kruskal2Minus :=
    fun n =>
      if n < h 0 then
        f n
      else
        g (n - h 0)
  -- The combined sequence would still be bad.
  have hcombBad : Kruskal2MinusBadSeq comb := by
    constructor
    · intro n; simp
    · intro m n hmn hEmbed
      by_cases hn : n < h 0
      -- Both indices are still in the original prefix of f.
      · have hm : m < h 0 := hmn.trans hn
        have hEmbed' : Kruskal2MinusEmbeds (f m) (f n) := by
          simpa [comb, hm, hn] using hEmbed
        exact hbad.2 m n hmn hEmbed'
      · have hnge : h 0 ≤ n := Nat.le_of_not_gt hn
        by_cases hm : m < h 0
        -- m is in the old prefix, while n is in the new support tail.
        · have hEmbed' : Kruskal2MinusEmbeds (f m) (g (n - h 0)) := by
            simpa [comb, hm, hn] using hEmbed
          have hIntoParent : Kruskal2MinusEmbeds (g (n - h 0)) (f (h (n - h 0))) :=
            hgEmbedParent (n - h 0)
          have hWhole : Kruskal2MinusEmbeds (f m) (f (h (n - h 0))) :=
            Kruskal2MinusEmbeds_trans hEmbed' hIntoParent
          have hmParent : m < h (n - h 0) :=
            lt_of_lt_of_le hm  (hh (n - h 0))
          exact hbad.2 m (h (n - h 0)) hmParent hWhole
        -- Both indices lie in the bad support tail g.
        · have hmge : h 0 ≤ m := Nat.le_of_not_gt hm
          have hsub : m - h 0 < n - h 0 := by omega
          have hEmbed' : Kruskal2MinusEmbeds (g (m - h 0)) (g (n - h 0)) := by
            simpa [comb, hm, hn] using hEmbed
          exact hgBad.2 (m - h 0) (n - h 0) hsub hEmbed'
  -- comb agrees with f strictly before the replacement position.
  have hprefix : ∀ m < h 0, f m = comb m := by
    intro m hm; simp [comb, hm]
  -- At the replacement position we inserted g(0).
  have hcombAt : comb (h 0) = g 0 := by simp [comb]
  -- g(0) is strictly smaller than the parent which it supports.
  have hsmall : Kruskal2Minus_cmplx (comb (h 0)) < Kruskal2Minus_cmplx (f (h 0)) := by
    rw [hcombAt, hgNode 0]
    exact Kruskal2Minus_cmplx_lt_node_of_occurs (hgOccurs 0)
  -- This contradicts minimality of f at position h(0).
  have hnotBad : ¬ Kruskal2MinusBadSeq comb := (hmin (h 0)) comb hprefix hsmall
  exact hnotBad hcombBad

-- Kruskal Trees with Base Labels in a Set
-- Every base label occurring in t belongs to S
def KruskalBasesOn {X : Type} (S : Set X) (t : KruskalTree X) : Prop :=
  ∀ x, KruskalBaseOccurs x t → x ∈ S
-- Every base label occurring in a forest belongs to S
def KruskalForestBasesOn {X : Type} (S : Set X) (ts : List (KruskalTree X)) : Prop :=
  ∀ t, t ∈ ts → KruskalBasesOn S t

-- Trees over the Subtype S
mutual
-- Forget the proof that every base label belongs to S
@[simp] def KruskalSubtypeErase {X : Type} {S : Set X} :
        KruskalTree S → KruskalTree X
  | .base x => .base x.1
  | .node ts => .node (KruskalSubtypeEraseList ts)
termination_by
  t => 2 * KruskalTree.transComplexity t
decreasing_by
  all_goals
    subst_vars
    try have htPos : 0 < KruskalTree.transComplexity t :=
      KruskalTree.transComplexity_pos t
    simp [KruskalTree.transComplexity, KruskalTree.transComplexityList] at * <;> omega
-- Forget subtype proofs componentwise in a forest
@[simp] def KruskalSubtypeEraseList {X : Type} {S : Set X} :
        List (KruskalTree S) → List (KruskalTree X)
  | [] => []
  | t :: ts => KruskalSubtypeErase t :: KruskalSubtypeEraseList ts
termination_by
  ts => 2 * KruskalTree.transComplexityList ts + 1
decreasing_by
  all_goals
    subst_vars
    try have htPos : 0 < KruskalTree.transComplexity t :=
      KruskalTree.transComplexity_pos t
    simp [KruskalTree.transComplexity, KruskalTree.transComplexityList] at * <;> omega

end
-- Erasing subtype proofs commutes with concatenation of forests
@[simp]
theorem KruskalSubtypeEraseList_append {X : Type} {S : Set X}
        (ss ts : List (KruskalTree S)) :
        KruskalSubtypeEraseList (ss ++ ts) =
          KruskalSubtypeEraseList ss ++ KruskalSubtypeEraseList ts := by
  induction ss with
  | nil =>
      simp [KruskalSubtypeEraseList]
  | cons s ss ih =>
      simp [KruskalSubtypeEraseList, ih]

-- Erasing Subtype Proofs Preserves Embedding
mutual
-- Forgetting subtype proofs preserves Kruskal tree embedding
theorem KruskalSubtypeErase_embeds {X : Type} {S : Set X} {r : X → X → Prop}
        {s t : KruskalTree S}
        (h : KruskalTreeEmbeds (fun x y : S => r x.1 y.1) s t) :
        KruskalTreeEmbeds r (KruskalSubtypeErase s) (KruskalSubtypeErase t) := by
  cases h with
  | base hxy =>
      simpa using KruskalTreeEmbeds.base hxy
  | @root ss ts hforest =>
      subst_vars
      simpa using KruskalTreeEmbeds.root
        (KruskalSubtypeEraseList_embeds hforest)
  | @descend s t before after hsub =>
      subst_vars
      simpa using KruskalTreeEmbeds.descend
        (before := KruskalSubtypeEraseList before)
        (after := KruskalSubtypeEraseList after)
        (KruskalSubtypeErase_embeds hsub)
termination_by
  2 * (KruskalTree.transComplexity s + KruskalTree.transComplexity t)
decreasing_by
  all_goals
    subst_vars
    simp [KruskalTree.transComplexity, KruskalTree.transComplexityList,
      KruskalTree.transComplexityList_append]
    omega
-- Forgetting subtype proofs preserves Kruskal forest embedding
theorem KruskalSubtypeEraseList_embeds {X : Type} {S : Set X} {r : X → X → Prop}
        {ss ts : List (KruskalTree S)}
        (h : KruskalForestEmbeds (fun x y : S => r x.1 y.1) ss ts) :
        KruskalForestEmbeds r
          (KruskalSubtypeEraseList ss) (KruskalSubtypeEraseList ts) := by
  cases h with
  | nil =>
      rw [KruskalSubtypeEraseList]
      exact KruskalForestEmbeds.nil
  | @cons s t ss before after hst hrest =>
      have hrest' := KruskalSubtypeEraseList_embeds hrest
      rw [KruskalSubtypeEraseList_append] at hrest'
      simpa using KruskalForestEmbeds.cons
        (before := KruskalSubtypeEraseList before)
        (after := KruskalSubtypeEraseList after)
        (KruskalSubtypeErase_embeds hst)
        hrest'
termination_by
  2 * (KruskalTree.transComplexityList ss +
    KruskalTree.transComplexityList ts) + 1
decreasing_by
  all_goals
    subst_vars
    try have hsPos : 0 < KruskalTree.transComplexity s :=
      KruskalTree.transComplexity_pos s
    try have htPos : 0 < KruskalTree.transComplexity t :=
      KruskalTree.transComplexity_pos t
    simp [KruskalTree.transComplexity, KruskalTree.transComplexityList,
      KruskalTree.transComplexityList_append] at *
    omega
end

-- Lift Trees Whose Bases Lie in S to Trees over the Subtype S
mutual
-- A tree whose bases all lie in S can be viewed as a Kruskal tree over the subtype S
theorem exists_KruskalSubtypeLift {X : Type} {S : Set X} {t : KruskalTree X}
        (ht : KruskalBasesOn S t) :
        ∃ u : KruskalTree S, KruskalSubtypeErase u = t := by
  cases t with
  | base x =>
      have hx : x ∈ S := ht x KruskalBaseOccurs.base
      refine ⟨.base ⟨x, hx⟩, ?_⟩
      simp
  | node ts =>
      have hts : KruskalForestBasesOn S ts := by
        intro t htMem
        intro x hx
        exact ht x (KruskalBaseOccurs.node htMem hx)
      obtain ⟨us, hus⟩ := exists_KruskalSubtypeLiftList hts
      refine ⟨.node us, ?_⟩
      simpa using congrArg KruskalTree.node hus
termination_by
  2 * KruskalTree.transComplexity t
decreasing_by
  all_goals
    subst_vars
    simp [KruskalTree.transComplexity, KruskalTree.transComplexityList]
    omega
-- A forest whose bases all lie in S can be viewed as a forest over the subtype S
theorem exists_KruskalSubtypeLiftList {X : Type} {S : Set X}
        {ts : List (KruskalTree X)}
        (hts : KruskalForestBasesOn S ts) :
        ∃ us : List (KruskalTree S), KruskalSubtypeEraseList us = ts := by
  cases ts with
  | nil =>
      refine ⟨[], ?_⟩
      simp
  | cons t ts =>
      have ht : KruskalBasesOn S t :=
        hts t List.mem_cons_self
      have htail : KruskalForestBasesOn S ts := by
        intro u hu
        exact hts u (List.mem_cons_of_mem t hu)
      obtain ⟨u, hu⟩ := exists_KruskalSubtypeLift ht
      obtain ⟨us, hus⟩ := exists_KruskalSubtypeLiftList htail
      refine ⟨u :: us, ?_⟩
      simp [KruskalSubtypeEraseList, hu, hus]
termination_by
  2 * KruskalTree.transComplexityList ts + 1
decreasing_by
  all_goals
    subst_vars
    have htPos : 0 < KruskalTree.transComplexity t :=
      KruskalTree.transComplexity_pos t
    simp [KruskalTree.transComplexity, KruskalTree.transComplexityList] at * <;> omega
end

-- Restricted Kruskal Theorem
-- If S is WQO, then Kruskal trees whose base labels all lie in S are WQO
theorem KruskalTreeEmbeds_partiallyWellOrderedOn_of_bases
        {X : Type} {r : X → X → Prop} [IsPreorder X r] {S : Set X}
        (hS : S.PartiallyWellOrderedOn r) :
        {t : KruskalTree X | KruskalBasesOn S t}.PartiallyWellOrderedOn
          (KruskalTreeEmbeds r) := by
  classical
  let rS : S → S → Prop := fun x y => r x.1 y.1
  letI : IsPreorder S rS :=
    { refl := by
        intro x
        exact refl_of r x.1
      trans := by
        intro x y z hxy hyz
        exact trans_of r hxy hyz }
  have hSubtype : WellQuasiOrdered rS := by
    rw [← Set.partiallyWellOrderedOn_univ_iff]
    rw [Set.partiallyWellOrderedOn_iff_exists_lt]
    rw [Set.partiallyWellOrderedOn_iff_exists_lt] at hS
    intro g _
    obtain ⟨i, j, hij, hrel⟩ :=
      hS (fun n => (g n).1) (fun n => (g n).2)
    exact ⟨i, j, hij, hrel⟩
  have hKruskal : WellQuasiOrdered (KruskalTreeEmbeds rS) :=
    KruskalTreeEmbeds_wqo hSubtype
  rw [Set.partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  have hLift : ∀ n, ∃ t : KruskalTree S, KruskalSubtypeErase t = f n := by
    intro n
    exact exists_KruskalSubtypeLift (hf n)
  choose g hg using hLift
  obtain ⟨i, j, hij, hEmbed⟩ := hKruskal g
  have hErase :
      KruskalTreeEmbeds r
        (KruskalSubtypeErase (g i))
        (KruskalSubtypeErase (g j)) :=
    KruskalSubtypeErase_embeds hEmbed
  refine ⟨i, j, hij, ?_⟩
  simpa [hg i, hg j] using hErase

-- Children of a Minimal Bad T₂⁻ Sequence are WQO
-- The immediate T₂ children of a minimal bad T₂⁻ sequence form a WQO set
theorem Kruskal2ChildrenOfMinBad_partiallyWellOrderedOn
        {f : ℕ → Kruskal2Minus}
        (hbad : Kruskal2MinusBadSeq f)
        (hmin : ∀ n, Kruskal2MinusMinBadSeq n f) :
        (Kruskal2ChildrenOfSeq f).PartiallyWellOrderedOn Kruskal2Embeds := by
  have hSupport :
      (Kruskal2SupportOfSeq f).PartiallyWellOrderedOn
        Kruskal2MinusEmbeds :=
    Kruskal2SupportOfMinBad_partiallyWellOrderedOn hbad hmin
  have hSupportedTrees :
      {t : Kruskal2 |
        KruskalBasesOn (Kruskal2SupportOfSeq f) t}.PartiallyWellOrderedOn
          Kruskal2Embeds :=
    KruskalTreeEmbeds_partiallyWellOrderedOn_of_bases hSupport
  rw [Set.partiallyWellOrderedOn_iff_exists_lt] at hSupportedTrees ⊢
  intro R hR
  apply hSupportedTrees R
  intro n
  obtain ⟨p, ts, hpNode, hpMem⟩ := hR n
  intro x hx
  exact ⟨p, ts, hpNode, ⟨R n, hpMem, hx⟩⟩

-- WQO of T₂⁻
-- The label-0 objects of the two-level Kruskal construction are WQO
theorem Kruskal2MinusEmbeds_wqo :
        WellQuasiOrdered Kruskal2MinusEmbeds := by
  classical
  rw [← Set.partiallyWellOrderedOn_univ_iff]
  rw [Set.PartiallyWellOrderedOn.iff_not_exists_isMinBadSeq
    Kruskal2Minus_cmplx]
  rintro ⟨f, hbad, hmin⟩
  have hChildren :
      (Kruskal2ChildrenOfSeq f).PartiallyWellOrderedOn Kruskal2Embeds :=
    Kruskal2ChildrenOfMinBad_partiallyWellOrderedOn hbad hmin
  have hNode : ∀ n, ∃ ts : List Kruskal2, f n = .node ts := by
    intro n
    cases hfn : f n with
    | node ts =>
        exact ⟨ts, rfl⟩
  choose forests hForests using hNode
  have hForestOn :
      ∀ n, KruskalTree.KruskalForestOn
        (Kruskal2ChildrenOfSeq f) (forests n) := by
    intro n t ht
    exact ⟨n, forests n, hForests n, ht⟩
  have hForestWQO :
      {ts : List Kruskal2 |
        KruskalTree.KruskalForestOn
          (Kruskal2ChildrenOfSeq f) ts}.PartiallyWellOrderedOn
            Kruskal2ForestEmbeds :=
    KruskalTree.KruskalForestEmbeds_partiallyWellOrderedOn hChildren
  rw [Set.partiallyWellOrderedOn_iff_exists_lt] at hForestWQO
  obtain ⟨i, j, hij, hForestEmbed⟩ :=
    hForestWQO forests hForestOn
  have hRootEmbed :
      Kruskal2MinusEmbeds (f i) (f j) := by
    rw [hForests i, hForests j]
    exact Kruskal2MinusEmbeds.root hForestEmbed
  exact hbad.2 i j hij hRootEmbed

-- WQO of the Full Two-Level Kruskal Construction
-- The full two-level Kruskal construction is WQO
theorem Kruskal2Embeds_wqo :
        WellQuasiOrdered Kruskal2Embeds := by
  exact KruskalTreeEmbeds_wqo Kruskal2MinusEmbeds_wqo


end GapTree


















-- Well-foundedness of NormalPrincipal follows from well-foundedness of NormalFreundTerm.
theorem NormalPrincipal_lt_wf (hGap : WellQuasiOrdered GapTreeEmbeds) :
        WellFounded NormalPrincipal_lt := by
  apply (WellFounded.onFun (f := BHToFreund.NormalPrincipal_toFreund)
        (NormalFreundTerm_lt_wf hGap)).mono
  intro p q hpq
  exact BHToFreund.NormalPrincipal_toFreund_lt hpq
-- Well-foundedness of NormalCountableOrd follows from the strong-gap WQO.
theorem NormalCountableOrd_lt_wf_of_gap_wqo (hGap : WellQuasiOrdered GapTreeEmbeds) :
        WellFounded NormalCountableOrd_lt := by
  exact NormalCountableOrd_lt_wf_of_principal_wf (NormalPrincipal_lt_wf hGap)
-- Strong-gap well-quasi-ordering of finite two-labelled trees.
axiom GapTreeEmbeds_wqo : WellQuasiOrdered GapTreeEmbeds
-- Well-foundedness of the normal countable ordinal notation system.
theorem NormalCountableOrd_lt_wf : WellFounded NormalCountableOrd_lt := by
  exact NormalCountableOrd_lt_wf_of_gap_wqo GapTreeEmbeds_wqo


--========================================================================================
-- Some Notes
--========================================================================================
/- When using existing complexity measurements such as trees and paths, it does not fully capture
   the detailed complexity of our notion. This leads to a circular argument and we cannot prove the
   desceding property needed to show well-foundedness. We look at Ferna ndez-Duque and Weiermann's
   paper for insight and attempt to bring in more mathematical objects needed.
-/





/-
--========================================================================================
-- Some Notes
--========================================================================================
/-
We tried two methods of measuring the complexity of our notations. One was by (1) defining a single
natural-number structural complexity measuring the total syntactic size of a term, and the other was
by (2) defining a recursive lexicographic rank that mirrors the term’s exponent–coefficient–r
emainder structure so comparison decreases by the first differing coordinate. However, both reach
the same problem : a ciruclar proof. We try a different method. We attempt to map our
notations to some field, which is already assured to be well-ordered, in an order preserving manner.
-/
/-
The outline is follows:
1. Define the canonical evaluation
2. Show Equality is preserved through the evaluation mapping
3. Define the evaluation of the coefficient
4. Prove every semantic coefficient is below Ω
   Important concept Pohler introduces is the collapsing function to map the Ω-normal form
   to ordinals under Ω
-/

--========================================================================================
-- Mapping the Notation to Ordinal (Lean)
--========================================================================================
--========================================================================================
-- Semantic interpretation into Mathlib ordinals

noncomputable section
-- Ω is the first uncountable ordinal ω₁
def BH_Omega : Ordinal := Ordinal.omega 1
-- P = {ω ^ α : α ∈ Ord}
def BN_P : Set Ordinal := Set.range (fun α : Ordinal => Ordinal.omega0 ^ α)
end

mutual
noncomputable def countableOrd_evalWith (theta : Ordinal → Ordinal) : countableOrd → Ordinal
  | .sum ps => principalList_evalWith theta ps
noncomputable def principal_evalWith (theta : Ordinal → Ordinal) : principal → Ordinal
  | .psi a => theta (omegaTerm_evalWith theta a)
noncomputable def principalList_evalWith (theta : Ordinal → Ordinal) : List principal → Ordinal
  | [] => 0
  | p :: ps => principal_evalWith theta p + principalList_evalWith theta ps
noncomputable def omegaTerm_evalWith (theta : Ordinal → Ordinal) : omegaTerm → Ordinal
  | .zero => 0
  | .omegaNF alpha beta gamma =>
    BH_Omega ^ omegaTerm_evalWith theta alpha * countableOrd_evalWith theta beta +
    omegaTerm_evalWith theta gamma
end

--========================================================================================
-- Equality is preserved

mutual
theorem countableOrd_eq_evalWith_eq (theta : Ordinal → Ordinal) {a b : countableOrd} (h : a=cb) :
        countableOrd_evalWith theta a = countableOrd_evalWith theta b := by
  cases h with
  | sum pListEq => simp only [countableOrd_evalWith]
                   exact principalList_eq_evalWith_eq theta pListEq
theorem principal_eq_evalWith_eq (theta : Ordinal → Ordinal) {p q : principal} (h : p =p q) :
        principal_evalWith theta p = principal_evalWith theta q := by
  cases h with
  | psi harg => simp only [principal_evalWith]
                rw [omegaTerm_eq_evalWith_eq theta harg]
theorem principalList_eq_evalWith_eq (theta : Ordinal → Ordinal) {ps qs : List principal}
        (h : principalList_eq ps qs) :
        principalList_evalWith theta ps = principalList_evalWith theta qs := by
  cases h with
  | nil => rfl
  | cons head tail =>
    simp only [principalList_evalWith]
    rw [principal_eq_evalWith_eq theta head, principalList_eq_evalWith_eq theta tail]
theorem omegaTerm_eq_evalWith_eq (theta : Ordinal → Ordinal) {a b : omegaTerm} (h : a =o b) :
        omegaTerm_evalWith theta a = omegaTerm_evalWith theta b := by
  cases h with
  | zero => rfl
  | omegaNF alpha beta gamma =>
    simp only [omegaTerm_evalWith]
    rw [omegaTerm_eq_evalWith_eq theta alpha, countableOrd_eq_evalWith_eq theta beta,
        omegaTerm_eq_evalWith_eq theta gamma]
end

--========================================================================================
-- Some properties

-- countbaleOrd 0 maps to Lean ordinal 0
@[simp]
theorem countableOrd_evalWith_zero (theta : Ordinal → Ordinal) :
        countableOrd_evalWith theta countableOrd.zero = 0 := by rfl

-- Unfold the evaluation of ψ(a)
@[simp]
theorem principal_evalWith_psi (theta : Ordinal → Ordinal) (o : omegaTerm) :
        principal_evalWith theta (.psi o) = theta (omegaTerm_evalWith theta o) := by
  rfl

-- List principal [] maps to Lean ordinal 0
@[simp]
theorem principalList_evalWith_nil (theta : Ordinal → Ordinal) :
        principalList_evalWith theta [] = 0 := by rfl

-- Break up the evaluation of a list
@[simp]
theorem principalList_evalWith_cons (theta : Ordinal → Ordinal) (p : principal)
        (ps : List principal) :
        principalList_evalWith theta (p :: ps) =
        principal_evalWith theta p + principalList_evalWith theta ps := by rfl

-- Transformation of principal and countableOrd and its equality
@[simp]
theorem countableOrd_evalWith_ofPrincipal (theta : Ordinal → Ordinal) (p : principal) :
        countableOrd_evalWith theta (countableOrd.ofPrincipal p) = principal_evalWith theta p := by
  simp [countableOrd.ofPrincipal,
        countableOrd_evalWith,
        principalList_evalWith]

-- omegaTerm 0 maps to Lean ordinal 0
@[simp]
theorem omegaTerm_evalWith_zero (theta : Ordinal → Ordinal) :
        omegaTerm_evalWith theta omegaTerm.zero = 0 := by rfl

-- Evaluation of omegaNF
@[simp]
theorem omegaTerm_evalWith_omegaNF (theta : Ordinal → Ordinal) (a g : omegaTerm)
        (b : countableOrd) :
        omegaTerm_evalWith theta (.omegaNF a b g) =
        BH_Omega ^ omegaTerm_evalWith theta a * countableOrd_evalWith theta b +
        omegaTerm_evalWith theta g := by rfl

--===============================================================================
-- Semantic coefficient set C(ξ) and maximal coefficient ξ*
--===============================================================================
/- For an Ω-normal form ζ = Ω^{α}β + γ, Pohlers defines a function
        C(0) = {0}, C(Ω^{α}β + γ) = C(α) ∪ C(γ) ∪ {β}
   and the maximal coefficient ζ^* := max C(ζ) -/

-- BHCoeff (ζ, c) to mean c ∈ C (ζ)
inductive BHCoeff : Ordinal → Ordinal → Prop where
  | zero : BHCoeff 0 0
  -- ξ = Ω^{e}c → c ∈ C(ζ)
  | coefficient {ξ e c : Ordinal} (h : (e, c) ∈ Ordinal.CNF BH_Omega ξ) : BHCoeff ξ c
  -- ξ = Ω^{e}c → d ∈ C(e) → d ∈ C(ζ)
  | exponent {ξ e c d : Ordinal} (hpair : (e, c) ∈ Ordinal.CNF BH_Omega ξ) (hd : BHCoeff e d) :
    BHCoeff ξ d

-- We define the set of coefficients (which is an ordinal ofc) if ξ
def BH_C (ξ : Ordinal) : Set Ordinal := {c | BHCoeff ξ c}

-- Retrieve the max coefficient (and its evaluated value) from a notation
noncomputable def BH_star (ξ : Ordinal) : Ordinal := sSup (BH_C ξ)

theorem BH_C_zero : 0 ∈ BH_C 0 := by exact BHCoeff.zero
theorem BH_C_of_CNF {ξ e c : Ordinal} (h : (e, c) ∈ Ordinal.CNF BH_Omega ξ) : c ∈ BH_C ξ := by
  exact BHCoeff.coefficient h
theorem BH_C_of_exponent {ξ e c d : Ordinal} (hpair : (e, c) ∈ Ordinal.CNF BH_Omega ξ)
        (hd : d ∈ BH_C e) : d ∈ BH_C ξ := by
  exact BHCoeff.exponent hpair hd

--===============================================================================
-- Mapping to under Ω
--===============================================================================
-- 1 < Ω
theorem BH_Omega_one_lt : (1 : Ordinal) < BH_Omega := by
  have h1 : (1 : Ordinal) < Ordinal.omega0 := Ordinal.one_lt_omega0
  have h2 : Ordinal.omega0 < Ordinal.omega 1 := Ordinal.omega0_lt_omega_one
  exact lt_trans h1 h2

-- every coefficient of ξ is less than Ω
theorem BHCoeff_lt_Omega {ξ c : Ordinal} (h : BHCoeff ξ c) : c < BH_Omega := by
  induction h with
  | zero => exact Ordinal.omega_pos 1
  | coefficient hcnf => exact Ordinal.CNF.snd_lt BH_Omega_one_lt hcnf
  | exponent hpair hd ih => exact ih

theorem BH_C_lt_Omega {ξ c : Ordinal} (hc : c ∈ BH_C ξ) : c < BH_Omega := by
  exact BHCoeff_lt_Omega hc

-- The set of coefficients of ξ is bounded above
theorem BH_C_bddAbove (ξ : Ordinal) : BddAbove (BH_C ξ) := by
  refine ⟨BH_Omega, ?_⟩; intro c hc; exact le_of_lt (BH_C_lt_Omega hc)

-- Every coefficient is less than the max
theorem BH_C_le_star {ξ c : Ordinal} (hc : c ∈ BH_C ξ) : c ≤ BH_star ξ := by
  unfold BH_star; exact le_csSup (BH_C_bddAbove ξ) hc

-- Prove that for any ordinal, it coefficient set is nonempty
theorem BH_C_nonempty (ξ : Ordinal) : (BH_C ξ).Nonempty := by
  by_cases hξ : ξ = 0
  · subst ξ -- goal : (BH_C 0).Nonempty
    exact ⟨0, BH_C_zero⟩
  · have hcnf : (Ordinal.log BH_Omega ξ, ξ / BH_Omega ^ Ordinal.log BH_Omega ξ) ∈
                Ordinal.CNF BH_Omega ξ := by
      rw [Ordinal.CNF.ne_zero hξ]
      exact List.mem_cons_self
    exact ⟨ξ / BH_Omega ^ Ordinal.log BH_Omega ξ, BH_C_of_CNF hcnf⟩

-- The max coefficient is less or equal to than Ω
theorem BH_star_le_Omega (ξ : Ordinal) : BH_star ξ ≤ BH_Omega := by
  unfold BH_star
  apply csSup_le (BH_C_nonempty ξ)
  intro c hc
  exact le_of_lt (BH_C_lt_Omega hc)

/- If d ∈ C(ξ), then
      (1) ξ = 0 and d = 0,
      (2) there exists e such that ξ = Ω^{e}d,
      (3) there exist e and c such that ξ = Ω^{e}c, e < ξ, and d ∈ C(e) -/
theorem BHCoeff_reduce {ξ d : Ordinal} (h : BHCoeff ξ d) :
        (ξ = 0 ∧ d = 0) ∨ (∃ e, (e, d) ∈ Ordinal.CNF BH_Omega ξ) ∨
        (∃ e c, (e, c) ∈ Ordinal.CNF BH_Omega ξ ∧ e < ξ ∧ BHCoeff e d) := by
  induction h with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  -- {ξ e c : Ordinal} (hcnf : (e, c) ∈ Ordinal.CNF BH_Omega ξ)
  | @coefficient ξ e c hcnf => exact Or.inr (Or.inl ⟨e, hcnf⟩)
  -- {ξ e c d : Ordinal} (hpair : (e, c) ∈ Ordinal.CNF BH_Omega ξ) (hd : BHCoeff e d)
  | @exponent ξ e c d hpair hd ih =>
    have he_le : e ≤ ξ := by
      exact le_trans (Ordinal.CNF.fst_le_log hpair) (Ordinal.log_le_self BH_Omega ξ)
    rcases lt_or_eq_of_le he_le with he_lt | he_eq
    · exact Or.inr (Or.inr ⟨e, c, hpair, he_lt, hd⟩)
    · subst e; exact ih

-- The coefficient set is finite
theorem BH_C_finite (ξ : Ordinal) : (BH_C ξ).Finite := by
  classical
  refine WellFoundedLT.induction (motive := fun ξ => (BH_C ξ).Finite) ξ ?_
  intro ξ ih
  let pairs : Finset (Ordinal × Ordinal) := (Ordinal.CNF BH_Omega ξ).toFinset
  let exps : Finset Ordinal := pairs.image Prod.fst
  let direct : Finset Ordinal := pairs.image Prod.snd
  let inherited : Finset Ordinal :=
    exps.biUnion fun e =>
      if he : e < ξ then
        (ih e he).toFinset
      else
        ∅
  let cover : Finset Ordinal := insert 0 (direct ∪ inherited)
  apply cover.finite_toSet.subset
  intro d hd
  change BHCoeff ξ d at hd
  rcases BHCoeff_reduce hd with hzero | hdirect | hinherited
  · rcases hzero with ⟨_, rfl⟩; simp [cover]
  · rcases hdirect with ⟨e, hpair⟩
    have hpair' : (e, d) ∈ pairs := by simpa [pairs] using hpair
    have hd_direct : d ∈ direct := by
      refine Finset.mem_image.mpr ?_
      exact ⟨(e, d), hpair', rfl⟩
    simp [cover, hd_direct]
  · rcases hinherited with ⟨e, c, hpair, he, hed⟩
    have hpair' : (e, c) ∈ pairs := by
      simpa [pairs] using hpair
    have he_exps : e ∈ exps := by
      refine Finset.mem_image.mpr ?_
      exact ⟨(e, c), hpair', rfl⟩
    have hedC : d ∈ BH_C e := hed
    have hd_inherited : d ∈ inherited := by
      simp only [inherited, Finset.mem_biUnion]
      refine ⟨e, he_exps, ?_⟩
      simp [he, hedC]
    simp [cover, hd_inherited]

-- The max coefficient is less than Ω
theorem BH_star_lt_Omega (ξ : Ordinal) : BH_star ξ < BH_Omega := by
  unfold BH_star
  rw [Set.Finite.csSup_lt_iff (BH_C_finite ξ) (BH_C_nonempty ξ)]
  intro c hc
  exact BH_C_lt_Omega hc


--========================================================================================
-- Theta condition
/- The paper we are looking at defines theta(ξ) := Θ_{P}(ξ) as the least principal ordinal θ
   satisfying ξ^* < θ < Ω and ∀ ζ < ξ, ζ^* < θ → theta (ζ) < θ.
-/

/- Assuming f defines the collapsed values of ordinals under ξ, θ is an acceptable
   candidate for the collapsed value of ξ
   (θ ∈ P) ∧ (ξ^* < θ) ∧ (θ < Ω) ∧ (∀ ζ < ξ)[ζ^* < θ → f(ζ) < θ] -/
def BHThetaCond (f : Ordinal → Ordinal) (ξ θ : Ordinal) : Prop :=
  θ ∈ BN_P ∧ BH_star ξ < θ ∧ θ < BH_Omega ∧ ∀ ζ, ζ < ξ → BH_star ζ < θ → f ζ < θ

/- Set of all ordinals θ that are valid candidates for the collapse value of ξ, assuming
   f gives the already-defined earlier collapse values -/
def BHThetaCandidates (f : Ordinal → Ordinal) (ξ : Ordinal) : Set Ordinal :=
  {θ | BHThetaCond f ξ θ}



-/




/-
--========================================================================================
-- Structural Complexity 2 (Rank)
--========================================================================================
/- Outline
    1. Definition
    2. Evaluation
    3. Defining Comparison
    4. Some Properties
    5. Rank of Normal Objects
    6. Packaging Normal Objects with Normal Rank
    7. Some Properties
-/
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
-- 1. Definition
--========================================================================================
mutual
inductive CountableOrdRank where
  | sum : List PrincipalRank → CountableOrdRank
inductive PrincipalRank where
  | psi : OmegaTermRank → PrincipalRank
inductive OmegaTermRank where
  | zero : OmegaTermRank
  | omegaNF : OmegaTermRank → CountableOrdRank → OmegaTermRank → OmegaTermRank
end

namespace OmegaTermRank
def coefficients : OmegaTermRank → List CountableOrdRank
  | .zero =>
      [.sum []]
  | .omegaNF alpha beta gamma =>
      coefficients alpha ++ coefficients gamma ++ [beta]
end OmegaTermRank

--========================================================================================
-- 2. Evaluation
--========================================================================================
mutual
def countableOrd_rank : countableOrd → CountableOrdRank
  | countableOrd.sum ps => CountableOrdRank.sum (principalList_rank ps)
def principal_rank : principal → PrincipalRank
  | principal.psi a => PrincipalRank.psi (omegaTerm_rank a)
def principalList_rank : List principal → List PrincipalRank
  | [] => []
  | p :: ps => principal_rank p :: principalList_rank ps
def omegaTerm_rank : omegaTerm → OmegaTermRank
  | omegaTerm.zero => OmegaTermRank.zero
  | omegaTerm.omegaNF alpha beta gamma =>
    OmegaTermRank.omegaNF (omegaTerm_rank alpha) (countableOrd_rank beta)
      (omegaTerm_rank gamma)
end

-- Evaluation Identities ---------------------------------------------------------------
-- Some data conversions
@[simp]
theorem countableOrd_rank_sum (ps : List principal) :
        countableOrd_rank (countableOrd.sum ps) =
        CountableOrdRank.sum (principalList_rank ps) := by
  rfl
@[simp]
theorem principalList_rank_nil : principalList_rank [] = [] := by
  rfl
@[simp]
theorem principalList_rank_cons (p : principal) (ps : List principal) :
        principalList_rank (p :: ps) = principal_rank p :: principalList_rank ps := by
  rfl
@[simp]
theorem omegaTerm_rank_zero : omegaTerm_rank omegaTerm.zero = OmegaTermRank.zero := by rfl
@[simp]
theorem omegaTerm_rank_omegaNF (alpha gamma : omegaTerm) (beta : countableOrd) :
        omegaTerm_rank (.omegaNF alpha beta gamma) =
        .omegaNF (omegaTerm_rank alpha) (countableOrd_rank beta) (omegaTerm_rank gamma) := by rfl
@[simp]
theorem omegaTerm_rank_coefficients (o : omegaTerm) :
        (omegaTerm.coefficients o).map countableOrd_rank =
          OmegaTermRank.coefficients (omegaTerm_rank o) := by
  cases o with
  | zero =>
      simp [omegaTerm.coefficients, omegaTerm_rank, OmegaTermRank.coefficients, countableOrd.zero,
            countableOrd_rank, principalList_rank]
  | omegaNF alpha beta gamma =>
      have hAlpha := omegaTerm_rank_coefficients alpha
      have hGamma := omegaTerm_rank_coefficients gamma
      simp [omegaTerm.coefficients, omegaTerm_rank, OmegaTermRank.coefficients, List.map_append,
            hAlpha, hGamma]
-- Equality preserves rank
mutual
theorem countableOrd_eq_rank_eq {a b : countableOrd} (h : a=cb) : countableOrd_rank a =
        countableOrd_rank b := by
  cases h with
  | sum hps =>
      simp only [countableOrd_rank]
      apply congrArg CountableOrdRank.sum
      exact principalList_eq_rank_eq hps
  termination_by
    countableOrd_cmplx a + countableOrd_cmplx b
  decreasing_by
    all_goals
      subst_vars
      simp only [countableOrd_cmplx]
      omega
theorem principal_eq_rank_eq {p q : principal} (h : p=pq) :
        principal_rank p = principal_rank q := by
  cases p with
  | psi a =>
    cases q with
    | psi b =>
      cases h with
      | psi habOmega =>
        simp only [principal_rank]
        exact congrArg PrincipalRank.psi (omegaTerm_eq_rank_eq habOmega)
  termination_by
    principal_cmplx p + principal_cmplx q
  decreasing_by
    all_goals
      subst_vars
      simp only [principal_cmplx]
      omega
theorem principalList_eq_rank_eq {pList qList : List principal} (h : principalList_eq pList qList) :
        principalList_rank pList = principalList_rank qList := by
  cases h with
  | nil => simp [principalList_rank]
  | cons hHead hTail =>
    simp only [principalList_rank]
    rw [principal_eq_rank_eq hHead, principalList_eq_rank_eq hTail]
  termination_by
    principalList_cmplx pList + principalList_cmplx qList
  decreasing_by
    all_goals
      subst_vars
      simp only [principalList_cmplx]
      omega
theorem omegaTerm_eq_rank_eq {a b : omegaTerm} (h : a=ob) : omegaTerm_rank a = omegaTerm_rank b
        := by
  cases h with
  | zero => simp [omegaTerm_rank]
  | omegaNF alphaEq betaEq gammaEq =>
    change
      OmegaTermRank.omegaNF (omegaTerm_rank _) (countableOrd_rank _) (omegaTerm_rank _) =
      OmegaTermRank.omegaNF (omegaTerm_rank _) (countableOrd_rank _) (omegaTerm_rank _)
    rw [omegaTerm_eq_rank_eq alphaEq, countableOrd_eq_rank_eq betaEq, omegaTerm_eq_rank_eq gammaEq]
  termination_by
    omegaTerm_cmplx a + omegaTerm_cmplx b
  decreasing_by
    all_goals
      subst_vars
      simp only [omegaTerm_cmplx]
      omega

theorem omegaTerm_eq_coefficient_rank_eq {a b : omegaTerm} (h : a =o b) :
        (omegaTerm.coefficients a).map countableOrd_rank
        = (omegaTerm.coefficients b).map countableOrd_rank := by
  cases h with
  | zero => simp [OmegaTermRank.coefficients, omegaTerm_rank,
                  omegaTerm.coefficients, countableOrd_rank,
                  principalList_rank, countableOrd.zero]
  | omegaNF alphaEq betaEq gammaEq =>
    simp only [omegaTerm.coefficients, List.map_append, List.map_cons, List.map_nil]
    rw [omegaTerm_eq_coefficient_rank_eq alphaEq,
        omegaTerm_eq_coefficient_rank_eq gammaEq,
        countableOrd_eq_rank_eq betaEq]
  termination_by
    omegaTerm_cmplx a + omegaTerm_cmplx b
  decreasing_by
    all_goals
      subst_vars
      simp only [omegaTerm_cmplx]
      omega
end
--========================================================================================
-- 3. Comparison
--========================================================================================
mutual
inductive CountableOrdRank_lt : CountableOrdRank → CountableOrdRank → Prop where
  | sum {xs ys : List PrincipalRank} (h : PrincipalListRank_lt xs ys) :
    CountableOrdRank_lt (.sum xs) (.sum ys)
inductive PrincipalRank_lt : PrincipalRank → PrincipalRank → Prop where
  | psi_forward {a b : OmegaTermRank}
                (harg : OmegaTermRank_lt a b)
                (hcoeff : OmegaTermCoefficientRank_lt
                  (OmegaTermRank.coefficients a) (.sum [.psi b])) :
                PrincipalRank_lt (.psi a) (.psi b)
  | psi_reverse_lt {a b : OmegaTermRank} {c : CountableOrdRank}
                   (harg : OmegaTermRank_lt b a)
                   (hc : c ∈ OmegaTermRank.coefficients b)
                   (hbound : CountableOrdRank_lt (.sum [.psi a]) c) :
                   PrincipalRank_lt (.psi a) (.psi b)
  | psi_reverse_eq {a b : OmegaTermRank} {c : CountableOrdRank}
                   (harg : OmegaTermRank_lt b a)
                   (hc : c ∈ OmegaTermRank.coefficients b)
                   (hbound : (.sum [.psi a] : CountableOrdRank) = c) :
                   PrincipalRank_lt (.psi a) (.psi b)
inductive PrincipalListRank_lt : List PrincipalRank → List PrincipalRank → Prop where
  | nil {p : PrincipalRank} {ps : List PrincipalRank} : PrincipalListRank_lt [] (p :: ps)
  | head {p q : PrincipalRank} {ps qs : List PrincipalRank} (h : PrincipalRank_lt p q) :
    PrincipalListRank_lt (p :: ps) (q :: qs)
  | tail {p q : PrincipalRank} {ps qs : List PrincipalRank} (heq : p = q)
         (htail : PrincipalListRank_lt ps qs) :
         PrincipalListRank_lt (p :: ps) (q :: qs)
inductive OmegaTermRank_lt : OmegaTermRank → OmegaTermRank → Prop where
  | zero {alpha gamma : OmegaTermRank} {beta : CountableOrdRank} :
    OmegaTermRank_lt .zero (.omegaNF alpha beta gamma)
  | exponent {alpha1 alpha2 gamma1 gamma2 : OmegaTermRank} {beta1 beta2 : CountableOrdRank}
             (h : OmegaTermRank_lt alpha1 alpha2) :
    OmegaTermRank_lt (.omegaNF alpha1 beta1 gamma1) (.omegaNF alpha2 beta2 gamma2)
  | coefficient {alpha1 alpha2 gamma1 gamma2 : OmegaTermRank} {beta1 beta2 : CountableOrdRank}
                (hexeq : alpha1 = alpha2) (h : CountableOrdRank_lt beta1 beta2) :
    OmegaTermRank_lt (.omegaNF alpha1 beta1 gamma1) (.omegaNF alpha2 beta2 gamma2)
  | remainder {alpha1 alpha2 gamma1 gamma2 : OmegaTermRank} {beta1 beta2 : CountableOrdRank}
              (hexeq : alpha1 = alpha2) (hcoeq : beta1 = beta2)
              (h : OmegaTermRank_lt gamma1 gamma2) :
    OmegaTermRank_lt (.omegaNF alpha1 beta1 gamma1) (.omegaNF alpha2 beta2 gamma2)
-- Comparison of list of coefficients with a single value
inductive OmegaTermCoefficientRank_lt : List CountableOrdRank → CountableOrdRank → Prop where
  | nil {bound : CountableOrdRank} : OmegaTermCoefficientRank_lt [] bound
  | cons {c bound : CountableOrdRank} {cs : List CountableOrdRank}
         (hhead : CountableOrdRank_lt c bound) (htail : OmegaTermCoefficientRank_lt cs bound) :
    OmegaTermCoefficientRank_lt (c :: cs) bound
end
--========================================================================================
-- 3. Some Properties
--========================================================================================
/-
The crucial relation is that the original raw data comparison is preserved onto their ranks
-/
mutual
theorem countableOrd_lt_rank_lt {a b : countableOrd} (h : a<cb) :
        CountableOrdRank_lt (countableOrd_rank a) (countableOrd_rank b) := by
  cases h with
  | sum hList => exact CountableOrdRank_lt.sum (principalList_lt_rank_lt hList)
  termination_by
    countableOrd_cmplx a + countableOrd_cmplx b
  decreasing_by
    all_goals
      subst_vars
      simp only [countableOrd_cmplx]
      omega
theorem principal_lt_rank_lt {p q : principal} (h : p<pq) :
        PrincipalRank_lt (principal_rank p) (principal_rank q) := by
  cases h with
  | @psi_forward a b hArg hCoeff =>
      apply PrincipalRank_lt.psi_forward
      · exact omegaTerm_lt_rank_lt hArg
      · have hCoeffRank :=
          coefficientList_lt_rank_lt hCoeff
        simpa [principal_rank, countableOrd.ofPrincipal] using hCoeffRank
  | @psi_reverse_lt a b c hArg hc hBound =>
      apply PrincipalRank_lt.psi_reverse_lt
      · exact omegaTerm_lt_rank_lt hArg
      · have hcMap :
            countableOrd_rank c ∈
              (omegaTerm.coefficients b).map countableOrd_rank := by
          exact List.mem_map.mpr ⟨c, hc, rfl⟩
        simpa using hcMap
      · have hBoundRank :=
          countableOrd_lt_rank_lt hBound
        simpa [principal_rank, countableOrd.ofPrincipal] using hBoundRank
  | @psi_reverse_eq a b c hArg hc hBound =>
      apply PrincipalRank_lt.psi_reverse_eq
      · exact omegaTerm_lt_rank_lt hArg
      · have hcMap :
            countableOrd_rank c ∈
              (omegaTerm.coefficients b).map countableOrd_rank := by
          exact List.mem_map.mpr ⟨c, hc, rfl⟩
        simpa using hcMap
      · have hBoundRank := countableOrd_eq_rank_eq hBound
        simpa [
          principal_rank,
          countableOrd.ofPrincipal
        ] using hBoundRank
  termination_by principal_cmplx p + principal_cmplx q
  decreasing_by
    all_goals
      subst_vars
      try have hCoeffCmplx := coefficients_cmplx_lt a
      try have hcCmplx := coefficient_cmplx_lt_of_mem hc
      simp only [principal_cmplx, countableOrd_cmplx_ofPrincipal_psi] at *
      omega
theorem principalList_lt_rank_lt {ps qs : List principal} (h : principalList_lt ps qs) :
        PrincipalListRank_lt (principalList_rank ps) (principalList_rank qs) := by
  cases h with
  | nil => exact PrincipalListRank_lt.nil
  | head hHead => exact PrincipalListRank_lt.head (principal_lt_rank_lt hHead)
  | tail hHeadEq hTail =>
      exact PrincipalListRank_lt.tail
        (principal_eq_rank_eq hHeadEq)
        (principalList_lt_rank_lt hTail)
  termination_by principalList_cmplx ps + principalList_cmplx qs
  decreasing_by
    all_goals
      subst_vars
      simp only [principalList_cmplx]
      omega
theorem omegaTerm_lt_rank_lt {a b : omegaTerm} (h : a <o b) :
    OmegaTermRank_lt (omegaTerm_rank a) (omegaTerm_rank b) := by
  cases h with
  | zero => exact OmegaTermRank_lt.zero
  | exponent hAlpha =>
      exact OmegaTermRank_lt.exponent
        (omegaTerm_lt_rank_lt hAlpha)
  | coefficient hAlphaEq hBeta =>
      exact OmegaTermRank_lt.coefficient
        (omegaTerm_eq_rank_eq hAlphaEq)
        (countableOrd_lt_rank_lt hBeta)
  | remainder hAlphaEq hBetaEq hGamma =>
      exact OmegaTermRank_lt.remainder
        (omegaTerm_eq_rank_eq hAlphaEq)
        (countableOrd_eq_rank_eq hBetaEq)
        (omegaTerm_lt_rank_lt hGamma)
  termination_by omegaTerm_cmplx a + omegaTerm_cmplx b
  decreasing_by
    all_goals
      subst_vars
      simp only [omegaTerm_cmplx]
      omega
theorem coefficientList_lt_rank_lt {cs : List countableOrd} {bound : countableOrd}
        (h : coefficientList_lt cs bound) :
        OmegaTermCoefficientRank_lt (cs.map countableOrd_rank)
        (countableOrd_rank bound) := by
  cases h with
  | nil => exact OmegaTermCoefficientRank_lt.nil
  | cons hHead hTail =>
      simp only [List.map_cons]
      exact OmegaTermCoefficientRank_lt.cons
        (countableOrd_lt_rank_lt hHead)
        (coefficientList_lt_rank_lt hTail)
  termination_by coefficientList_cmplx cs + countableOrd_cmplx bound
  decreasing_by
    all_goals
      subst_vars
      simp only [coefficientList_cmplx]
      omega
end
--========================================================================================
-- 4. Rank of Normal Objects
--========================================================================================
-- Rank of normal objects
def NormalCountableOrd_rank (a : NormalCountableOrd) : CountableOrdRank :=
  countableOrd_rank a.1
def NormalPrincipal_rank (p : NormalPrincipal) : PrincipalRank :=
  principal_rank p.1
def NormalPrincipalList_rank
    (ps : NormalPrincipalList) : List PrincipalRank :=
  principalList_rank ps.1
def NormalOmegaTerm_rank (o : NormalOmegaTerm) : OmegaTermRank :=
  omegaTerm_rank o.1
--===============================================================================
-- Normal equality preserves rank
theorem NormalCountableOrd_eq_rank_eq {a b : NormalCountableOrd} (h : a =nc b) :
        NormalCountableOrd_rank a = NormalCountableOrd_rank b := by
  exact countableOrd_eq_rank_eq h
theorem NormalPrincipal_eq_rank_eq {p q : NormalPrincipal} (h : p=npq) :
        NormalPrincipal_rank p = NormalPrincipal_rank q := by
  exact principal_eq_rank_eq h
theorem NormalPrincipalList_eq_rank_eq {ps qs : NormalPrincipalList}
        (h : NormalPrincipalList_eq ps qs) : NormalPrincipalList_rank ps =
        NormalPrincipalList_rank qs := by
  exact principalList_eq_rank_eq h
theorem NormalOmegaTerm_eq_rank_eq {a b : NormalOmegaTerm} (h : a=nob) :
        NormalOmegaTerm_rank a = NormalOmegaTerm_rank b := by
  exact omegaTerm_eq_rank_eq h

--===============================================================================
-- Normal < is preserved by rank
theorem NormalCountableOrd_lt_rank_lt {a b : NormalCountableOrd} (h : a <nc b) :
        CountableOrdRank_lt (NormalCountableOrd_rank a) (NormalCountableOrd_rank b) := by
  exact countableOrd_lt_rank_lt h
theorem NormalPrincipal_lt_rank_lt {p q : NormalPrincipal} (h : p<npq) :
        PrincipalRank_lt (NormalPrincipal_rank p) (NormalPrincipal_rank q) := by
  exact principal_lt_rank_lt h
theorem NormalPrincipalList_lt_rank_lt {ps qs : NormalPrincipalList}
        (h : NormalPrincipalList_lt ps qs) :
        PrincipalListRank_lt (NormalPrincipalList_rank ps)
          (NormalPrincipalList_rank qs) := by
  exact principalList_lt_rank_lt h
theorem NormalOmegaTerm_lt_rank_lt {a b : NormalOmegaTerm} (h : a<nob) :
        OmegaTermRank_lt (NormalOmegaTerm_rank a) (NormalOmegaTerm_rank b) := by
  exact omegaTerm_lt_rank_lt h
--===============================================================================
-- Well-Foundedness of rank
theorem PrincipalListRank_nil_acc : Acc PrincipalListRank_lt [] := by
  apply Acc.intro -- Goal : ∀pr : PrincipalListRank, PrincipalListRank_lt pr [] →
  intro pr hlt
  cases hlt
theorem OmegaTermRank_zero_acc : Acc OmegaTermRank_lt .zero := by
  apply Acc.intro
  intro or hlt
  cases hlt
def PrincipalListRank_bounded_by (p : PrincipalRank) (ps : List PrincipalRank) : Prop :=
  ∀ q, q ∈ ps → PrincipalRank_lt q p ∨ q = p
/-
Given OmegaTermRank a b g, if the following two statements hold
  (i) for any a' < a, for any b' g' OmegaTerm.omegaNF a' b' g' is accessible
  (ii) for any b' < b (a' = a), for any g' OmegaTerm.omegaNF a b' g is accessible
then, we must have OmegaTerm.omegaNF a b g is accessible
-/
theorem OmegaTermRank_omegaNF_acc {a : OmegaTermRank} {b : CountableOrdRank}
        {g : OmegaTermRank}
        (hAlpha : ∀ a', OmegaTermRank_lt a' a → ∀ b' g', Acc OmegaTermRank_lt (.omegaNF a' b' g'))
        (hBeta : ∀ b', CountableOrdRank_lt b' b → ∀ g', Acc OmegaTermRank_lt (.omegaNF a b' g'))
        (hGamma : Acc OmegaTermRank_lt g) :
        Acc OmegaTermRank_lt (.omegaNF a b g) := by
  induction hGamma with
  -- g : OmegaTermRank
  -- hpred : ∀ y, y < g → Acc OmegaTermRank_lt y
  -- ih : ∀ y, y < g → Acc OmegaTermRank_lt (.omegaNF a b y)
  | intro g hpred ih =>
    apply Acc.intro --∀x:OmegaTermRank, OmegaTermRank_lt x (.omegaNF a b g) → Acc---
    intro x hx -- Goal : Acc OmegaTermRank_lt x
    cases hx with
    -- x.alpha < a
    | zero => exact OmegaTermRank_zero_acc
    | exponent ha => exact hAlpha _ ha _ _
    | coefficient haeq hb => subst_vars; exact hBeta _ hb _
    | remainder haeq hbeq hc => subst_vars; exact ih _ hc
/- Say we have an arbitrary coefficient list of an omegaTerm. We represent the rank list as cs.
   If that rank list is bounded above, then any rank of the list is bounded by the same
-/
theorem OmegaTermCoefficientRank_lt_of_mem {cs : List CountableOrdRank} {bound c : CountableOrdRank}
        (h : OmegaTermCoefficientRank_lt cs bound) (hc : c ∈ cs) :
        CountableOrdRank_lt c bound := by
  induction cs with
  | nil => simp at hc
  | cons x xs ih => cases h with
                    | cons hhead htail =>
                      simp only [List.mem_cons] at hc
                      rcases hc with rfl | hc
                      · exact hhead
                      · exact ih htail hc
theorem CountableOrdRank_acc_of_list_acc {ps : List PrincipalRank}
        (hps : Acc PrincipalListRank_lt ps) :
        Acc CountableOrdRank_lt (.sum ps) := by
  induction hps with
  | intro ps hpred ih =>
    apply Acc.intro -- ∀a : CountableOrdRank, CountableOrdRank_lt a (.sum ps) → Acc -- a
    intro a ha
    cases a with
    | sum qs => cases ha with
                | sum hqs => exact ih qs hqs
theorem CountableOrdRank_singleton_lt {p q : PrincipalRank} (h : PrincipalRank_lt p q) :
        CountableOrdRank_lt (.sum [p]) (.sum [q]) := by
  exact CountableOrdRank_lt.sum (PrincipalListRank_lt.head h)
theorem PrincipalRank_acc_of_singleton_acc (p : PrincipalRank)
        (hp : Acc CountableOrdRank_lt (.sum [p])) :
        Acc PrincipalRank_lt p := by
  have aux : ∀ a : CountableOrdRank, Acc CountableOrdRank_lt a →
             ∀ r : PrincipalRank, (.sum [r] : CountableOrdRank) = a →
             Acc PrincipalRank_lt r := by
    intro a ha
    induction ha with
    -- hpred : ∀b : CountableOrdRank, CountableOrdRank_lt b a → Acc CountableOrdRank_lt b
    /- ih : ∀b : CountableOrdRank, CountableOrdRank_lt b a →
                 (∀ r : PrincipalRank, (.sum [r] : CountableOrdRank) = b →
                  Acc PrincipalRank_lt r) -/
    | intro a hpred ih =>
      intro r hra -- Goal : Acc PrincipalRank_lt r
      apply Acc.intro
      /- Goal : ∀ s : PrincipalRank, PrincipalRank_lt s r → Acc PrincipalRank_lt →
                Acc PrincipalRank_lt s -/
      intro s hsr -- Goal Acc PrincipalRank_lt s
      have hsa : CountableOrdRank_lt (.sum [s]) a := by
        rw [← hra]
        exact CountableOrdRank_singleton_lt hsr
      exact ih (.sum [s]) hsa s rfl
  exact aux (.sum [p]) hp p rfl
--===============================================================================
-- Transitivity
--===============================================================================
-- Get the object from the rank
mutual
def countableOrd_of_rank (c : CountableOrdRank) : countableOrd :=
  match c with
  | .sum pListRank => .sum (principalList_of_rank pListRank)
def principal_of_rank (p : PrincipalRank) : principal :=
  match p with
  | .psi oRank => .psi (omegaTerm_of_rank oRank)
def principalList_of_rank (ps : List PrincipalRank) : List principal :=
  match ps with
  | [] => []
  | p :: ps => principal_of_rank p :: principalList_of_rank ps
def omegaTerm_of_rank (o : OmegaTermRank) : omegaTerm :=
  match o with
  | .zero => .zero
  | .omegaNF a b g => .omegaNF (omegaTerm_of_rank a) (countableOrd_of_rank b) (omegaTerm_of_rank g)
end
-- Ranking a decoded rank gives the original rank back
mutual
@[simp]
theorem countableOrd_rank_of_rank (a : CountableOrdRank) :
        countableOrd_rank (countableOrd_of_rank a) = a := by
  cases a with
  | sum pListRank => simp only [countableOrd_rank, countableOrd_of_rank]
                     rw [principalList_rank_of_rank]
@[simp]
theorem principal_rank_of_rank (p : PrincipalRank) :
        principal_rank (principal_of_rank p) = p :=  by
  cases p with
  | psi oRank => simp only [principal_rank, principal_of_rank]
                 rw [omegaTerm_rank_of_rank]
@[simp]
theorem principalList_rank_of_rank (ps : List PrincipalRank) :
        principalList_rank (principalList_of_rank ps) = ps := by
  cases ps with
  | nil => rfl
  | cons p ps => simp only [principalList_rank, principalList_of_rank]
                 rw [principal_rank_of_rank, principalList_rank_of_rank]
@[simp]
theorem omegaTerm_rank_of_rank (o : OmegaTermRank) :
        omegaTerm_rank (omegaTerm_of_rank o) = o := by
  cases o with
  | zero => rfl
  | omegaNF alpha beta gamma => simp only [omegaTerm_rank, omegaTerm_of_rank]
                                rw [omegaTerm_rank_of_rank, countableOrd_rank_of_rank,
                                    omegaTerm_rank_of_rank]
end
-- Decoding preserves the intrinsic coefficient list.

@[simp]
theorem omegaTerm_coefficients_of_rank (o : OmegaTermRank) :
        (OmegaTermRank.coefficients o).map countableOrd_of_rank =
        omegaTerm.coefficients (omegaTerm_of_rank o) := by
  cases o with
  | zero => rfl
  | omegaNF alpha beta gamma =>
    have ha := omegaTerm_coefficients_of_rank alpha
    have hg := omegaTerm_coefficients_of_rank gamma
    simp [OmegaTermRank.coefficients, omegaTerm_of_rank, omegaTerm.coefficients,
          List.map_append, ha, hg
]

theorem countableOrd_of_rank_cmplx_lt_of_coefficient
    {o : OmegaTermRank} {c : CountableOrdRank}
    (hc : c ∈ OmegaTermRank.coefficients o) :
    countableOrd_cmplx (countableOrd_of_rank c) + 2 <
      omegaTerm_cmplx (omegaTerm_of_rank o) := by
  have hc' : countableOrd_of_rank c ∈
      (OmegaTermRank.coefficients o).map countableOrd_of_rank :=
    List.mem_map.mpr ⟨c, hc, rfl⟩
  rw [omegaTerm_coefficients_of_rank] at hc'
  exact coefficient_cmplx_lt_of_mem hc'
/-
Convert each rank comparison back to the corresponding raw comparison.
Because equality inside the rank relations is Lean equality, equality cases
reduce with subst_vars and reflexivity of the raw custom equality.
-/
mutual
theorem CountableOrdRank_lt_to_raw {a b : CountableOrdRank} (h : CountableOrdRank_lt a b) :
        countableOrd_of_rank a <c countableOrd_of_rank b := by
  cases h with
  | sum psrlt =>
      simpa only [countableOrd_of_rank] using
        countableOrd_lt.sum (PrincipalListRank_lt_to_raw psrlt)
  termination_by
    countableOrd_cmplx (countableOrd_of_rank a) +
      countableOrd_cmplx (countableOrd_of_rank b)
  decreasing_by
    all_goals
      subst_vars
      simp only [countableOrd_of_rank, countableOrd_cmplx]
      omega
theorem PrincipalRank_lt_to_raw {p q : PrincipalRank} (h : PrincipalRank_lt p q) :
        principal_of_rank p <p principal_of_rank q := by
  cases h with
  | @psi_forward a b harg hcoeff =>
    simp only [principal_of_rank]
    apply principal_lt.psi_forward
    · exact OmegaTermRank_lt_to_raw harg
    · have hcoeff' := OmegaTermCoefficientRank_lt_to_raw hcoeff
      simpa [countableOrd_of_rank, principalList_of_rank, principal_of_rank,
             countableOrd.ofPrincipal] using hcoeff'
  | @psi_reverse_lt a b c harg hc hbound =>
      simp only [principal_of_rank]
      apply principal_lt.psi_reverse_lt
      · exact OmegaTermRank_lt_to_raw harg
      · have hc' : countableOrd_of_rank c ∈
                   (OmegaTermRank.coefficients b).map countableOrd_of_rank := by
          exact List.mem_map.mpr ⟨c, hc, rfl⟩
        simpa using hc'
      · have hbound' := CountableOrdRank_lt_to_raw hbound
        simpa [countableOrd_of_rank, principalList_of_rank, principal_of_rank,
               countableOrd.ofPrincipal] using hbound'
  | @psi_reverse_eq a b c harg hc hbound =>
      simp only [principal_of_rank]
      apply principal_lt.psi_reverse_eq
      · exact OmegaTermRank_lt_to_raw harg
      · have hc' : countableOrd_of_rank c ∈
                   (OmegaTermRank.coefficients b).map countableOrd_of_rank := by
          exact List.mem_map.mpr ⟨c, hc, rfl⟩
        simpa using hc'
      · have hdec : countableOrd_of_rank (.sum [.psi a]) =
                    countableOrd_of_rank c := congrArg countableOrd_of_rank hbound
        rw [← hdec]
        simpa [
          countableOrd_of_rank,
          principalList_of_rank,
          principal_of_rank,
          countableOrd.ofPrincipal
        ] using
          (countableOrd_eq_refl
            (countableOrd_of_rank (.sum [.psi a])))
  termination_by
    principal_cmplx (principal_of_rank p) +
      principal_cmplx (principal_of_rank q)
  decreasing_by
    all_goals
      subst_vars
      try have hCoeffCmplx := coefficients_cmplx_lt (omegaTerm_of_rank a)
      try have hcCmplx := countableOrd_of_rank_cmplx_lt_of_coefficient hc
      try rw [← omegaTerm_coefficients_of_rank a] at hCoeffCmplx
      simp only [principal_of_rank, principal_cmplx, countableOrd_of_rank,
        principalList_of_rank, countableOrd_cmplx, principalList_cmplx] at *
      omega
theorem PrincipalListRank_lt_to_raw
    {ps qs : List PrincipalRank}
    (h : PrincipalListRank_lt ps qs) :
    principalList_lt
      (principalList_of_rank ps)
      (principalList_of_rank qs) := by
  cases h with
  | nil =>
      simpa only [principalList_of_rank] using principalList_lt.nil

  | head hHead =>
      simpa only [principalList_of_rank] using
        principalList_lt.head (PrincipalRank_lt_to_raw hHead)

  | tail hEq hTail =>
      subst_vars
      simpa only [principalList_of_rank] using
        principalList_lt.tail (principal_eq_refl _)
          (PrincipalListRank_lt_to_raw hTail)
  termination_by
    principalList_cmplx (principalList_of_rank ps) +
      principalList_cmplx (principalList_of_rank qs)
  decreasing_by
    all_goals
      subst_vars
      simp only [principalList_of_rank, principalList_cmplx]
      omega

theorem OmegaTermRank_lt_to_raw
    {a b : OmegaTermRank}
    (h : OmegaTermRank_lt a b) :
    omegaTerm_of_rank a <o omegaTerm_of_rank b := by
  cases h with

  | zero =>
      simpa only [omegaTerm_of_rank] using omegaTerm_lt.zero

  | exponent hAlpha =>
      simpa only [omegaTerm_of_rank] using
        omegaTerm_lt.exponent (OmegaTermRank_lt_to_raw hAlpha)

  | coefficient hAlphaEq hBeta =>
      subst_vars
      simpa only [omegaTerm_of_rank] using
        omegaTerm_lt.coefficient (omegaTerm_eq_refl _)
          (CountableOrdRank_lt_to_raw hBeta)

  | remainder hAlphaEq hBetaEq hGamma =>
      subst_vars
      simpa only [omegaTerm_of_rank] using
        omegaTerm_lt.remainder (omegaTerm_eq_refl _)
          (countableOrd_eq_refl _) (OmegaTermRank_lt_to_raw hGamma)
  termination_by
    omegaTerm_cmplx (omegaTerm_of_rank a) +
      omegaTerm_cmplx (omegaTerm_of_rank b)
  decreasing_by
    all_goals
      subst_vars
      simp only [omegaTerm_of_rank, omegaTerm_cmplx]
      omega


theorem OmegaTermCoefficientRank_lt_to_raw
    {cs : List CountableOrdRank}
    {bound : CountableOrdRank}
    (h : OmegaTermCoefficientRank_lt cs bound) :
    coefficientList_lt
      (cs.map countableOrd_of_rank)
      (countableOrd_of_rank bound) := by
  cases h with
  | nil =>
      exact coefficientList_lt.nil
  | cons hHead hTail =>
      exact coefficientList_lt.cons
        (CountableOrdRank_lt_to_raw hHead)
        (OmegaTermCoefficientRank_lt_to_raw (bound := bound) hTail)
  termination_by
    coefficientList_cmplx (cs.map countableOrd_of_rank) +
      countableOrd_cmplx (countableOrd_of_rank bound)
  decreasing_by
    all_goals
      subst_vars
      simp only [List.map_cons, coefficientList_cmplx]
      omega
end

-- Transitivity
theorem CountableOrdRank_lt_trans {a b c : CountableOrdRank} (hab : CountableOrdRank_lt a b)
        (hbc : CountableOrdRank_lt b c) : CountableOrdRank_lt a c := by
  have hRaw : countableOrd_of_rank a <c countableOrd_of_rank c :=
    countableOrd_lt_trans (CountableOrdRank_lt_to_raw hab) (CountableOrdRank_lt_to_raw hbc)
  have hRank := countableOrd_lt_rank_lt hRaw
  simpa using hRank
theorem PrincipalRank_lt_trans {p q r : PrincipalRank} (hpq : PrincipalRank_lt p q)
        (hqr : PrincipalRank_lt q r) : PrincipalRank_lt p r := by
  have hRaw : principal_of_rank p <p principal_of_rank r :=
    principal_lt_trans (PrincipalRank_lt_to_raw hpq) (PrincipalRank_lt_to_raw hqr)
  have hRank := principal_lt_rank_lt hRaw
  simpa using hRank

--===============================================================================
-- 5. Rank-Normality
--===============================================================================

namespace CountableOrdRank
def zero : CountableOrdRank := .sum []
end CountableOrdRank
namespace PrincipalRank
def one : PrincipalRank :=
  .psi .zero
end PrincipalRank
namespace CountableOrdRank
def one : CountableOrdRank :=
  .sum [PrincipalRank.one]
end CountableOrdRank
mutual
inductive CountableOrdRank_normal : CountableOrdRank → Prop where
  | sum {ps : List PrincipalRank} (h : PrincipalListRank_normal ps) :
    CountableOrdRank_normal (.sum ps)
inductive PrincipalRank_normal : PrincipalRank → Prop where
  | psi {o : OmegaTermRank} (harg : OmegaTermRank_normal o)
        (hcoeff : OmegaTermCoefficientRank_lt
          (OmegaTermRank.coefficients o) (.sum [.psi o])) :
    PrincipalRank_normal (.psi o)
inductive PrincipalListRank_normal : List PrincipalRank → Prop where
  | nil : PrincipalListRank_normal []
  | singleton {p : PrincipalRank} (hp : PrincipalRank_normal p) :
    PrincipalListRank_normal [p]
  | cons {p q : PrincipalRank} {qs : List PrincipalRank} (hp : PrincipalRank_normal p)
         (htail : PrincipalListRank_normal (q :: qs))
         (horder : PrincipalRank_lt q p ∨ q = p) :
    PrincipalListRank_normal (p :: q :: qs)

inductive OmegaTermRank_normal : OmegaTermRank → Prop where
  | zero : OmegaTermRank_normal .zero
  | omegaNF {a g : OmegaTermRank} {b : CountableOrdRank} (ha : OmegaTermRank_normal a)
            (hb : CountableOrdRank_normal b) (hg : OmegaTermRank_normal g)
            (hpos : CountableOrdRank_lt CountableOrdRank.zero b)
            (hrem : OmegaTermRank_lt g (.omegaNF a CountableOrdRank.one .zero)):
            OmegaTermRank_normal (.omegaNF a b g)
end
def NormalCountableOrdRank := {a : CountableOrdRank // CountableOrdRank_normal a}
def NormalPrincipalRank := {p : PrincipalRank // PrincipalRank_normal p}
def NormalPrincipalListRank := {ps : List PrincipalRank // PrincipalListRank_normal ps}
def NormalOmegaTermRank := {o : OmegaTermRank // OmegaTermRank_normal o}
--Helpers
@[simp]
theorem countableOrd_rank_zero : countableOrd_rank countableOrd.zero = CountableOrdRank.zero := by
  rfl
@[simp]
theorem principal_rank_one : principal_rank principal.one = PrincipalRank.one := by
  rfl
@[simp]
theorem countableOrd_rank_one : countableOrd_rank countableOrd.one = CountableOrdRank.one := by
  rfl
-- If the object is normal, its rank is normal
mutual
theorem countableOrd_rank_normal {a : countableOrd} (ha : countableOrd_normal a) :
        CountableOrdRank_normal (countableOrd_rank a) := by
  cases ha with
  | sum hpList => simp only [countableOrd_rank]
                  exact CountableOrdRank_normal.sum (principalList_rank_normal hpList)
  termination_by countableOrd_cmplx a
  decreasing_by
    all_goals
      subst_vars
      simp only [
        countableOrd_cmplx,
        principal_cmplx,
        principalList_cmplx,
        omegaTerm_cmplx
      ]
      omega
theorem principal_rank_normal {p : principal} (hp : principal_normal p) :
        PrincipalRank_normal (principal_rank p) := by
  cases hp with
  | @psi a harg hcoeff => simp only [principal_rank]
                          apply PrincipalRank_normal.psi
                          · change OmegaTermRank_normal (omegaTerm_rank a)
                            exact omegaTerm_rank_normal harg
                          · have hc := coefficientList_lt_rank_lt hcoeff
                            rw [omegaTerm_rank_coefficients a] at hc
                            simpa [countableOrd.ofPrincipal,
                                   countableOrd_rank,
                                   principalList_rank,
                                   principal_rank
                                  ] using hc
  termination_by principal_cmplx p
  decreasing_by
    all_goals
      subst_vars
      simp only [
        countableOrd_cmplx,
        principal_cmplx,
        principalList_cmplx,
        omegaTerm_cmplx
      ]
      omega
theorem principalList_rank_normal {ps : List principal} (hps : principalList_normal ps) :
        PrincipalListRank_normal (principalList_rank ps) := by
  cases hps with
  | nil => exact PrincipalListRank_normal.nil
  | singleton hp => simp only [principalList_rank]
                    exact PrincipalListRank_normal.singleton (principal_rank_normal hp)
  | @cons p q qs hp htail horder =>
    simp only [principalList_rank]
    -- PrincipalListRank_normal (principal_rank p :: principal_rank q :: principalList_rank qs)
    apply PrincipalListRank_normal.cons
    · exact principal_rank_normal hp
    · exact principalList_rank_normal htail
    · cases horder with
      | inl hlt => exact Or.inl (principal_lt_rank_lt hlt)
      | inr heq => exact Or.inr (principal_eq_rank_eq heq).symm
  termination_by principalList_cmplx ps
  decreasing_by
    all_goals
      subst_vars
      simp only [
        countableOrd_cmplx,
        principal_cmplx,
        principalList_cmplx,
        omegaTerm_cmplx
      ]
      omega

theorem omegaTerm_rank_normal {o : omegaTerm} (ho : omegaTerm_normal o) :
        OmegaTermRank_normal (omegaTerm_rank o) := by
  cases ho with
  | zero =>
      exact OmegaTermRank_normal.zero
  | omegaNF ha hb hg hpos hrem =>
      refine OmegaTermRank_normal.omegaNF
        (omegaTerm_rank_normal ha)
        (countableOrd_rank_normal hb)
        (omegaTerm_rank_normal hg)
        ?_
        ?_
      · simpa using countableOrd_lt_rank_lt hpos
      · simpa using omegaTerm_lt_rank_lt hrem
  termination_by omegaTerm_cmplx o
  decreasing_by
    all_goals
      subst_vars
      simp only [
        countableOrd_cmplx,
        principal_cmplx,
        principalList_cmplx,
        omegaTerm_cmplx
      ]
      omega
end
--===============================================================================
-- 6.  Package normal objects into normal ranks
--===============================================================================

def NormalCountableOrd_toRank (a : NormalCountableOrd) : NormalCountableOrdRank :=
  ⟨NormalCountableOrd_rank a, countableOrd_rank_normal a.2⟩
def NormalPrincipal_toRank (p : NormalPrincipal) : NormalPrincipalRank :=
  ⟨NormalPrincipal_rank p, principal_rank_normal p.2⟩
def NormalPrincipalList_toRank (ps : NormalPrincipalList) : NormalPrincipalListRank :=
  ⟨NormalPrincipalList_rank ps, principalList_rank_normal ps.2⟩
def NormalOmegaTerm_toRank (o : NormalOmegaTerm) : NormalOmegaTermRank :=
  ⟨NormalOmegaTerm_rank o, omegaTerm_rank_normal o.2⟩


--===============================================================================
-- Comparison

def NormalCountableOrdRank_lt (a b : NormalCountableOrdRank) : Prop :=
  CountableOrdRank_lt a.1 b.1
def NormalPrincipalRank_lt (p q : NormalPrincipalRank) : Prop :=
  PrincipalRank_lt p.1 q.1
def NormalPrincipalListRank_lt (ps qs : NormalPrincipalListRank) : Prop :=
  PrincipalListRank_lt ps.1 qs.1
def NormalOmegaTermRank_lt (a b : NormalOmegaTermRank) : Prop :=
  OmegaTermRank_lt a.1 b.1

infix:50 " <ncr " => NormalCountableOrdRank_lt
infix:50 " <npr " => NormalPrincipalRank_lt
infix:50 " <nplr " => NormalPrincipalListRank_lt
infix:50 " <nor " => NormalOmegaTermRank_lt


--===============================================================================
-- 7. Some Properties
--===============================================================================
-- Original normal < is preserved by normal rank

theorem NormalCountableOrd_toRank_lt {a b : NormalCountableOrd} (h : a <nc b) :
    NormalCountableOrd_toRank a <ncr NormalCountableOrd_toRank b := by
  exact NormalCountableOrd_lt_rank_lt h

theorem NormalPrincipal_toRank_lt {p q : NormalPrincipal} (h : p<npq) :
        NormalPrincipal_toRank p <npr NormalPrincipal_toRank q := by
  exact NormalPrincipal_lt_rank_lt h

theorem NormalPrincipalList_toRank_lt {ps qs : NormalPrincipalList}
        (h : NormalPrincipalList_lt ps qs) :
        NormalPrincipalList_toRank ps <nplr NormalPrincipalList_toRank qs := by
  exact NormalPrincipalList_lt_rank_lt h

theorem NormalOmegaTerm_toRank_lt {a b : NormalOmegaTerm} (h : a<nob) :
        NormalOmegaTerm_toRank a <nor NormalOmegaTerm_toRank b := by
  exact NormalOmegaTerm_lt_rank_lt h


--===============================================================================
-- Well-foundedness of normal rank relations
--===============================================================================
--===============================================================================
-- Helper Lemmas
-- The head of the a normal PrincipalListRank is normal
theorem NormalPrincipalListRank_normalHead {p : PrincipalRank} {ps : List PrincipalRank}
        (h : PrincipalListRank_normal (p :: ps)) : PrincipalRank_normal p := by
  cases h with
  | singleton hp => exact hp
  | cons hp hps horder => exact hp
-- The tail of a normal PrincipalListRank is normal
theorem NormalPrincipalListRank_normalTail {p : PrincipalRank} {ps : List PrincipalRank}
        (h : PrincipalListRank_normal (p :: ps)) : PrincipalListRank_normal ps := by
  cases h with
  | singleton hp => exact PrincipalListRank_normal.nil
  | cons hp hps horder => exact hps
-- The head is the largest
theorem PrincipalListRank_normal_tail_bounded {p : PrincipalRank} {ps : List PrincipalRank}
        (h : PrincipalListRank_normal (p :: ps)) :
         ∀ q, q ∈ ps → PrincipalRank_lt q p ∨ q = p := by
  cases h with
  | singleton _ =>
      intro q hq
      simp at hq
  | cons _ hTail hOrder =>
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hOrder
      · rcases PrincipalListRank_normal_tail_bounded hTail r hr with hrq | hrq
        · rcases hOrder with hqp | hqp
          · exact Or.inl (PrincipalRank_lt_trans hrq hqp)
          · subst p
            exact Or.inl hrq
        · subst r
          exact hOrder

theorem NormalPrincipalListRank_nil_acc : Acc NormalPrincipalListRank_lt
        ⟨[], PrincipalListRank_normal.nil⟩ := by
  apply Acc.intro
  rintro ⟨ps, hps⟩ hlt
  cases hlt

theorem NormalOmegaTermRank_zero_acc : Acc NormalOmegaTermRank_lt
        ⟨OmegaTermRank.zero, OmegaTermRank_normal.zero⟩ := by
  apply Acc.intro
  rintro ⟨o, ho⟩ hlt
  cases hlt

theorem NormalCountableOrdRank_acc_of_lt {a b : NormalCountableOrdRank}
        (ha : Acc NormalCountableOrdRank_lt a)
        (hba : b <ncr a) : Acc NormalCountableOrdRank_lt b := by
  exact ha.inv hba

theorem NormalPrincipalRank_acc_of_lt {p q : NormalPrincipalRank}
        (hp : Acc NormalPrincipalRank_lt p) (hqp : q <npr p) :
        Acc NormalPrincipalRank_lt q := by
  exact hp.inv hqp

theorem NormalPrincipalListRank_acc_of_lt {ps qs : NormalPrincipalListRank}
        (hps : Acc NormalPrincipalListRank_lt ps) (hqs : qs <nplr ps) :
        Acc NormalPrincipalListRank_lt qs := by
  exact hps.inv hqs

theorem NormalOmegaTermRank_acc_of_lt {a b : NormalOmegaTermRank}
        (ha : Acc NormalOmegaTermRank_lt a) (hba : b <nor a) :
    Acc NormalOmegaTermRank_lt b := by
  exact ha.inv hba

theorem NormalPrincipalRank_acc_of_eq {p q : NormalPrincipalRank}
        (hp : Acc NormalPrincipalRank_lt p)
        (hpq : p.1 = q.1) : Acc NormalPrincipalRank_lt q := by
  have hpq' : p = q := by
    apply Subtype.ext
    exact hpq
  subst q
  exact hp

theorem NormalPrincipalListRank_cons_acc (p : NormalPrincipalRank)
        (hp : Acc NormalPrincipalRank_lt p)
        (hsmall : ∀ q : NormalPrincipalRank, q <npr p →
                  ∀ qs : NormalPrincipalListRank, PrincipalListRank_bounded_by q.1 qs.1 →
                  Acc NormalPrincipalListRank_lt qs)
        (ps : NormalPrincipalListRank) (hps : Acc NormalPrincipalListRank_lt ps)
        (hcons : PrincipalListRank_normal (p.1 :: ps.1)) :
        Acc NormalPrincipalListRank_lt ⟨p.1 :: ps.1, hcons⟩ := by
  induction hps generalizing p with
  -- hpred : ∀ys : NormalPrincipalListRank, ys <npr xs → Acc NormalPrincipalListRank_lt ys
  -- ih : ∀ys : NormalPrincipalListRank, ys <npr xs → (p) → (hp) → (hsmall) → (hcons) → goal
  | intro xs hpred ih =>
    apply Acc.intro -- goal : ∀ys : NormalPrincipalListRank, ys <nplr ⟨p.1 :: ps.1, hcons⟩ →
                    --        Acc NormalPrincipalListRank_lt ys
    rintro ⟨ys, hys_normal⟩ hlt -- hlt : ys <nplr ⟨p.1 :: ps.1, hcons⟩
                                -- goal : Acc NormalPrincipalListRank_lt ys
    cases ys with
    | nil => exact NormalPrincipalListRank_nil_acc
    | cons q qs => --ys = q :: qs
      change PrincipalListRank_lt (q :: qs) (p.1 :: xs.1) at hlt
      cases hlt with
      | head hqp =>
        -- hqp : q < p.1
        let qN : NormalPrincipalRank := ⟨q, NormalPrincipalListRank_normalHead hys_normal⟩
        apply hsmall qN hqp ⟨q :: qs, hys_normal⟩
        /- qN : NormalPrincipalRank, hqp :qN <npr p
           ys = ⟨q :: qs, hys_normal⟩ : NormalPrincipalListRank,
           New Goal : PrincipalListRank_bounded_by qN.1 ys.1 -/
        --  (qN.1 → ys.1 →) ∀ q, q ∈ ys.1 → PrincipalRank_lt q qN ∨ q = qN
        intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        -- hr : q ∈ (Tail of ys.1)
        · exact Or.inr rfl
        · exact PrincipalListRank_normal_tail_bounded hys_normal r hr
      | tail heq htail =>
        -- heq : (head of ys) = (head of ⟨p.1 :: ps.1, hcons⟩)
        -- htail : (tail of ys) = (tail of ⟨p.1 :: ps.1, hcons⟩)
        let qN : NormalPrincipalRank := ⟨q, NormalPrincipalListRank_normalHead hys_normal⟩
        let qsN : NormalPrincipalListRank := ⟨qs, NormalPrincipalListRank_normalTail hys_normal⟩
        have htailN : qsN <nplr xs := htail
        have hqAcc : Acc NormalPrincipalRank_lt qN := by
          apply NormalPrincipalRank_acc_of_eq hp
          exact heq.symm
        have hsmallQ : ∀ r : NormalPrincipalRank, r <npr qN →
                       ∀ rs : NormalPrincipalListRank, PrincipalListRank_bounded_by r.1 rs.1 →
                       Acc NormalPrincipalListRank_lt rs := by
          intro r hr rs hrs
          apply hsmall r
          /- new goal :
              q <npr p → ∀ rs : NormalPrincipalListRank, PrincipalListRank_bounded_by r.1 rs.1 -/
          · change PrincipalRank_lt r.1 p.1
            change PrincipalRank_lt r.1 q at hr
            simpa [heq] using hr
          · exact hrs
        exact ih qsN htailN qN hqAcc hsmallQ hys_normal


theorem NormalPrincipalListRank_acc_of_bound_acc (p : NormalPrincipalRank)
        (hp : Acc NormalPrincipalRank_lt p) (ps : NormalPrincipalListRank)
        (hbound : PrincipalListRank_bounded_by p.1 ps.1) :
        Acc NormalPrincipalListRank_lt ps := by
  revert ps -- Goal : (ps) → (hbound) → Acc NormalPrinciipalListRank_lt ps
  induction hp with
  -- hpred : ∀q : NormalPrincipalRank, q <npr p → Acc NormalPrincipalRank_lt q
  /- ih : ∀q : NormalPrincipalRank, q <npr p → (hq : Acc NormalPrincipalRank_lt q) →
          (qs : NormalPrincipalList Rank) → (hbound : PrincipalListRank_bounded_by q.1 qs.1)
          → Acc NormalPrincipalListRank_lt qs -/
  | intro p hpred ih =>
    rintro ⟨ps, hps⟩ hbound -- Goal : Acc NormalPrinciipalListRank_lt ⟨ps, hps⟩
    have proveList : ∀ xs : List PrincipalRank, ∀ hxs : PrincipalListRank_normal xs,
              PrincipalListRank_bounded_by p.1 xs →
              Acc NormalPrincipalListRank_lt ⟨xs, hxs⟩ := by
      intro xs /- Goal : ∀ hxs : PrincipalListRank_normal xs, PrincipalListRank_bounded_by p.1 xs →
                         Acc NormalPrincipalListRanK_lt ⟨xs, hxs⟩ -/
      induction xs with
      | nil => intro hxs hbound
               exact NormalPrincipalListRank_nil_acc
      -- xs = q :: qs
      /- ihTail : (∀ ys : List PrincipalRank, PrincipalListRank_lt ys xs (q :: qs) → )
                  ∀ hys : PrincipalListRank_normal ys →
                  PrincipalListRank_bounded_by p.1 ys →
                  Acc NormalPrincipalListRank_lt ⟨ys, hys⟩  -/
      | cons q qs ihTail =>
        intro hnormal hbound  -- hnormal : ∀ hxs : PrincipalListRank_normal xs
                              -- hbound : PrincipalListRank_bounded_by p.1 xs
                              -- Goal : Acc NormalPrincipalListRank_lt
        have hq_normal : PrincipalRank_normal q := NormalPrincipalListRank_normalHead hnormal
        have hqs_normal : PrincipalListRank_normal qs := NormalPrincipalListRank_normalTail hnormal
        let qN : NormalPrincipalRank := ⟨q, hq_normal⟩
        let qsN : NormalPrincipalListRank := ⟨qs, hqs_normal⟩
        -- qsN is accessible
        have hTailBounded : PrincipalListRank_bounded_by p.1 qs := by
          --  p → ps → ∀ q, q ∈ ps → PrincipalRank_lt q p ∨ q = p
          intro r hr /- hr : r ∈ qs
                        Goal : PrincipalRank_lt r p.1 ∨ r = p.1 -/
          exact hbound r (List.mem_cons_of_mem q hr)
        have htailAcc : Acc NormalPrincipalListRank_lt qsN := by
          exact ihTail hqs_normal hTailBounded
        have hqle : PrincipalRank_lt q p.1 ∨ q = p.1 :=
          hbound q List.mem_cons_self
        rcases hqle with hqp | hqeqp
        -- We apply NormalPrincipalListRank_cons_acc
        /- (p : NormalPrincipalRank) → (hp : Acc NormalPrincipalRank_lt p) →
           (hsmall : ∀ q : NormalPrincipalRank, q <npr p →
                  ∀ qs : NormalPrincipalListRank, PrincipalListRank_bounded_by q.1 qs.1 →
                  Acc NormalPrincipalListRank_lt qs) →
           (ps : NormalPrincipalListRank) → (hps : Acc NormalPrincipalListRank_lt ps) →
           (hcons : PrincipalListRank_normal (p.1 :: ps.1)) :
           Acc NormalPrincipalListRank_lt ⟨p.1 :: ps.1, hcons⟩-/
        -- We want qN accessible
        -- 1st case when hqp : PrincipalRank_lt q p.1
        · have hqAcc : Acc NormalPrincipalRank_lt qN :=
            hpred qN hqp
          have hqsmall : ∀ r : NormalPrincipalRank, r <npr qN →
                         ∀ rs : NormalPrincipalListRank, PrincipalListRank_bounded_by r.1 rs.1 →
                         Acc NormalPrincipalListRank_lt rs := by
            intro r hrqN rs hrsbound
            apply ih r /- new goal :  r <npr p → (hq : Acc NormalPrincipalRank_lt r) →
                                      (rs : NormalPrincipalList Rank) →
                                      (hbound : PrincipalListRank_bounded_by r.1 rs.1) -/
            · change PrincipalRank_lt r.1 p.1
              change PrincipalRank_lt r.1 q at hrqN
              exact PrincipalRank_lt_trans hrqN hqp
            · exact hrsbound
          exact NormalPrincipalListRank_cons_acc qN hqAcc hqsmall qsN htailAcc hnormal
        -- 2ns case when hqeqp : q = p.1 (same proof)
        · have hpAcc : Acc NormalPrincipalRank_lt p := Acc.intro p hpred
          have hqAcc : Acc NormalPrincipalRank_lt qN := by
            apply NormalPrincipalRank_acc_of_eq hpAcc
            exact hqeqp.symm
          have hqsmall : ∀ r : NormalPrincipalRank, r <npr qN →
                         ∀ rs : NormalPrincipalListRank, PrincipalListRank_bounded_by r.1 rs.1 →
                         Acc NormalPrincipalListRank_lt rs := by
            intro r hr rs hrs
            apply ih r
            · change PrincipalRank_lt r.1 p.1
              change PrincipalRank_lt r.1 q at hr
              rw [hqeqp] at hr
              exact hr
            · exact hrs
          exact NormalPrincipalListRank_cons_acc qN hqAcc hqsmall qsN htailAcc hnormal
    exact proveList ps hps hbound


-- If the head of a normal list is accessible, then the whole list is accessible.
theorem NormalPrincipalListRank_acc {p : PrincipalRank} {ps : List PrincipalRank}
        (hnormal : PrincipalListRank_normal (p :: ps))
        (hp : Acc NormalPrincipalRank_lt ⟨p, NormalPrincipalListRank_normalHead hnormal⟩) :
        Acc NormalPrincipalListRank_lt ⟨p :: ps, hnormal⟩ := by
  -- We use the previous theorem
  /- (p : NormalPrincipalRank) (hp : Acc NormalPrincipalRank_lt p) (ps : NormalPrincipalListRank)
     (hbound : PrincipalListRank_bounded_by p.1 ps.1) :
     Acc NormalPrincipalListRank_lt ps := by -/
  apply NormalPrincipalListRank_acc_of_bound_acc
        ⟨p, NormalPrincipalListRank_normalHead hnormal⟩ hp ⟨p :: ps, hnormal⟩
  -- new goal : PrincipalListRank_bounded_by p ps
  --            ∀ q, q ∈ ps → PrincipalRank_lt q p ∨ q = p
  intro q hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact Or.inr rfl
  · exact PrincipalListRank_normal_tail_bounded hnormal q hq

theorem NormalCountableOrdRank_acc {ps : NormalPrincipalListRank}
        (hps : Acc NormalPrincipalListRank_lt ps) :
        Acc NormalCountableOrdRank_lt ⟨CountableOrdRank.sum ps.1, CountableOrdRank_normal.sum ps.2⟩
        := by
  induction hps with
  -- hpred : ∀ qs : NPLR, qs < nplr ps → Acc NPLR qs
  -- ih : hpred → Acc NCOR_lt ⟨CountableOrdRank.sum qs.1, CountableOrdRank_normal.sum qs.2⟩
  | intro ps hpred ih =>
    apply Acc.intro
    /- new goal : ∀ rs : NCOR, NCOR_lt rs ⟨COR.sum ps.1, COR_normal.sum ps.2⟩
                  → Acc NCOR_lt ⟨COR.sum rs.1, COR_normal.sum rs.2⟩ -/
    rintro ⟨r, hr⟩ hlt
    cases r with
    | sum qs => cases hr with
                | sum hqsNormal => cases hlt with
                                   | sum hqsLt => exact ih ⟨qs, hqsNormal⟩ hqsLt

theorem CountableOrdRank_ofPrincipal_normal {p : PrincipalRank} (hp : PrincipalRank_normal p) :
        CountableOrdRank_normal (CountableOrdRank.sum [p]) := by
  apply CountableOrdRank_normal.sum
  exact PrincipalListRank_normal.singleton hp


def NormalPrincipalRank_toCountable (p : NormalPrincipalRank) : NormalCountableOrdRank :=
    ⟨CountableOrdRank.sum [p.1], CountableOrdRank_ofPrincipal_normal p.2⟩

theorem NormalPrincipalRank_toCountable_lt {p q : NormalPrincipalRank} (h : p <npr q) :
        NormalPrincipalRank_toCountable p <ncr NormalPrincipalRank_toCountable q := by
  change CountableOrdRank_lt (.sum [p.1]) (.sum [q.1])
  exact CountableOrdRank_lt.sum (PrincipalListRank_lt.head h)

theorem NormalPrincipalRank_acc_of_singleton_acc (p : NormalPrincipalRank)
        (hp : Acc NormalCountableOrdRank_lt (NormalPrincipalRank_toCountable p)) :
        Acc NormalPrincipalRank_lt p := by
  -- Proof strategy is to convert principal to countableOrd by embedding
  let embed : NormalPrincipalRank → NormalCountableOrdRank :=
    NormalPrincipalRank_toCountable
  have embed_lt {q r : NormalPrincipalRank} (hqr : q <npr r) : embed q <ncr embed r := by
    exact NormalPrincipalRank_toCountable_lt hqr
  have aux : ∀ a : NormalCountableOrdRank, Acc NormalCountableOrdRank_lt a →
             ∀ r : NormalPrincipalRank, embed r = a →
             Acc NormalPrincipalRank_lt r := by
    intro a ha -- goal : ∀ r : NormalPrincipalRank, embed r = a → Acc NormalPrincipalRank_lt r
    induction ha with
    -- hpred : ∀ b : NCOR, b < ncr a → Acc NCOR_lt b
    /- ih : ∀ b : NCOR, b < ncr a →
            ∀ r : NormalPrincipalRank, embed r = b →
            Acc NormalPrincipalRank_lt r -/
    | intro a hpred ih =>
      intro r hra -- new goal : Acc NormalPrincipalRank_lt r
      apply Acc.intro -- new goal : ∀ s : NPR, s <npr r → Acc NormalPrincipalRank_lt s
      intro s hsr -- new goal : Acc NormalPrincipalRank_lt s
      have hsa : embed s <ncr a := by rw [← hra]; exact embed_lt hsr
      exact ih (embed s) hsa s rfl
  exact aux (embed p) hp p rfl

theorem OmegaTermRank_normal_alpha {a g : OmegaTermRank} {b : CountableOrdRank}
        (h : OmegaTermRank_normal (.omegaNF a b g)) :
        OmegaTermRank_normal a := by
  cases h with
  | omegaNF ha _ _ _ _ => exact ha

theorem OmegaTermRank_normal_beta {a g : OmegaTermRank} {b : CountableOrdRank}
        (h : OmegaTermRank_normal (.omegaNF a b g)) :
        CountableOrdRank_normal b := by
  cases h with
  | omegaNF _ hb _ _ _ => exact hb

theorem OmegaTermRank_normal_gamma {a g : OmegaTermRank} {b : CountableOrdRank}
        (h : OmegaTermRank_normal (.omegaNF a b g)) :
        OmegaTermRank_normal g := by
  cases h with
  | omegaNF _ _ hg _ _ => exact hg

theorem OmegaTermRank_normal_beta_pos {a g : OmegaTermRank} {b : CountableOrdRank}
        (h : OmegaTermRank_normal (.omegaNF a b g)) :
        CountableOrdRank_lt CountableOrdRank.zero b := by
  cases h with
  | omegaNF _ _ _ hpos _ => exact hpos

theorem OmegaTermRank_normal_remainder_lt {a g : OmegaTermRank} {b : CountableOrdRank}
        (h : OmegaTermRank_normal (.omegaNF a b g)) :
        OmegaTermRank_lt g (.omegaNF a CountableOrdRank.one .zero) := by
  cases h with
  | omegaNF _ _ _ _ hrem => exact hrem

theorem OmegaTermRank_normal_coefficient {o : OmegaTermRank} (ho : OmegaTermRank_normal o)
        {c : CountableOrdRank} (hc : c ∈ OmegaTermRank.coefficients o) :
        CountableOrdRank_normal c := by
  cases o with
  | zero =>
      simp only [OmegaTermRank.coefficients, List.mem_singleton] at hc
      subst c
      exact CountableOrdRank_normal.sum PrincipalListRank_normal.nil
  | omegaNF a b g =>
      cases ho with
      | omegaNF ha hb hg hpos hrem =>
          simp only [OmegaTermRank.coefficients, List.mem_append,
                     List.mem_singleton] at hc
          rcases hc with (hcA | hcG) | hcB
          · exact OmegaTermRank_normal_coefficient ha hcA
          · exact OmegaTermRank_normal_coefficient hg hcG
          · subst c
            exact hb

theorem PrincipalRank_normal_coefficient {o : OmegaTermRank} (h : PrincipalRank_normal (.psi o))
        {c : CountableOrdRank} (hc : c ∈ OmegaTermRank.coefficients o) :
        CountableOrdRank_normal c := by
  cases h with
  | psi harg hcoeff =>
      exact OmegaTermRank_normal_coefficient harg hc

theorem NormalOmegaTermRank_omegaNF_acc {a g : OmegaTermRank} {b : CountableOrdRank}
        (hnormal : OmegaTermRank_normal (.omegaNF a b g))
        (hAlpha : ∀ a', OmegaTermRank_normal a' → OmegaTermRank_lt a' a →
                  ∀ b' g', ∀ hnormal' : OmegaTermRank_normal (.omegaNF a' b' g'),
                  Acc NormalOmegaTermRank_lt ⟨.omegaNF a' b' g', hnormal'⟩)
        (hBeta : ∀ b', CountableOrdRank_normal b' → CountableOrdRank_lt b' b →
                 ∀ g', ∀ hnormal' : OmegaTermRank_normal (.omegaNF a b' g'),
                 Acc NormalOmegaTermRank_lt ⟨.omegaNF a b' g', hnormal'⟩)
        (hGamma : Acc NormalOmegaTermRank_lt ⟨g, OmegaTermRank_normal_gamma hnormal⟩) :
        Acc NormalOmegaTermRank_lt ⟨.omegaNF a b g, hnormal⟩ := by
  have aux : ∀ gN : NormalOmegaTermRank, Acc NormalOmegaTermRank_lt gN →
             ∀ hnf : OmegaTermRank_normal (.omegaNF a b gN.1),
             Acc NormalOmegaTermRank_lt ⟨.omegaNF a b gN.1, hnf⟩ := by
    intro gN hgAcc -- goal : ∀ hnf : OmegaTermRank_normal (.omegaNF a b gN.1),
                   --        Acc NormalOmegaTermRank_lt ⟨.omegaNF a b gN.1, hnf⟩
    induction hgAcc with
    -- hpred : ∀ iN : NOTR, iN <nor gN → Acc NOTR_lt iN
    /- ih : ∀ iN : NOTR, iN <nor gN →
            ∀ hnf : OmegaTermRank_normal (.omegaNF a b iN.1),
             Acc NormalOmegaTermRank_lt ⟨.omegaNF a b iN.1, hnf⟩ -/
    | intro gN hpred ih =>
      intro hnf -- new goal : Acc NormalOmegaTermRank_lt ⟨.omegaNF a b gN.1, hnf⟩
      apply Acc.intro -- new goal : ∀ ⟨x, hxnormal⟩ < ⟨.omegaNF a b gN.1, hnf⟩ → Acc NOTR_lt ⟨x, hxnormal⟩
      rintro ⟨x, hxnormal⟩ hxlt
      -- hxlt : NormalOmegaTermRank_lt ⟨x, hxnormal⟩ ⟨.omegaNF a b gN.1, hnf⟩
      change OmegaTermRank_lt x (.omegaNF a b gN.1) at hxlt
      -- hxlt : OmegaTermRank_lt x (.omegaNF a b gN.1)
      cases hxlt with
      | zero => exact NormalOmegaTermRank_zero_acc
      | exponent ha => exact hAlpha _ (OmegaTermRank_normal_alpha hxnormal) ha _ _  hxnormal
      | coefficient haeq hb =>
        subst_vars
        exact hBeta _ (OmegaTermRank_normal_beta hxnormal) hb _ hxnormal
      | remainder haeq hbeq hg =>
        subst_vars
        let g'N : NormalOmegaTermRank := ⟨_, OmegaTermRank_normal_gamma hxnormal⟩
        have hgN : g'N <nor gN := by exact hg
        exact ih g'N hgN hxnormal
  exact aux ⟨g, OmegaTermRank_normal_gamma hnormal⟩ hGamma hnormal

mutual

theorem NormalCountableOrdRank_all_acc
    (a : NormalCountableOrdRank) :
    Acc NormalCountableOrdRank_lt a := by
  sorry


theorem NormalPrincipalRank_all_acc
    (p : NormalPrincipalRank) :
    Acc NormalPrincipalRank_lt p := by
  sorry


theorem NormalOmegaTermRank_all_acc
    (o : NormalOmegaTermRank) :
    Acc NormalOmegaTermRank_lt o := by
  sorry

end

theorem NormalPrincipalListRank_all_acc
    (ps : NormalPrincipalListRank) :
    Acc NormalPrincipalListRank_lt ps := by
  sorry

theorem NormalCountableOrdRank_lt_wf :
    WellFounded NormalCountableOrdRank_lt := by
  constructor
  intro a
  exact NormalCountableOrdRank_all_acc a


theorem NormalPrincipalRank_lt_wf :
    WellFounded NormalPrincipalRank_lt := by
  constructor
  intro p
  exact NormalPrincipalRank_all_acc p


theorem NormalPrincipalListRank_lt_wf :
    WellFounded NormalPrincipalListRank_lt := by
  constructor
  intro ps
  exact NormalPrincipalListRank_all_acc ps


theorem NormalOmegaTermRank_lt_wf :
    WellFounded NormalOmegaTermRank_lt := by
  constructor
  intro o
  exact NormalOmegaTermRank_all_acc o


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
  have embed_lt {q r : NormalPrincipal} (hqr : q <np r) : embed q <nc embed r := by
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
-/
