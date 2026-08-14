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


-- -------------------------------------------------------------------------------
-- 9. Accessibility helper for a normal omegaNF rank
--
-- This is the normal-rank analogue of OmegaTermRank_omegaNF_acc.
-- -------------------------------------------------------------------------------

theorem NormalOmegaTermRank_omegaNF_acc
    {a g : OmegaTermRank}
    {b : CountableOrdRank}
    (hnormal :
      OmegaTermRank_normal (.omegaNF a b g))
    (hAlpha :
      ∀ a',
        OmegaTermRank_normal a' →
        OmegaTermRank_lt a' a →
        ∀ b' g',
          OmegaTermRank_normal (.omegaNF a' b' g') →
          Acc NormalOmegaTermRank_lt
            ⟨.omegaNF a' b' g', by assumption⟩)
    (hBeta :
      ∀ b',
        CountableOrdRank_normal b' →
        CountableOrdRank_lt b' b →
        ∀ g',
          OmegaTermRank_normal (.omegaNF a b' g') →
          Acc NormalOmegaTermRank_lt
            ⟨.omegaNF a b' g', by assumption⟩)
    (hGamma :
      Acc NormalOmegaTermRank_lt
        ⟨g, OmegaTermRank_normal_gamma hnormal⟩) :
    Acc NormalOmegaTermRank_lt
      ⟨.omegaNF a b g, hnormal⟩ := by
  sorry


-- -------------------------------------------------------------------------------
-- 10. Global accessibility of normal ranks
--
-- These are the main theorems.
-- -------------------------------------------------------------------------------

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


-- Once all normal principals are accessible, all normal principal lists follow.

theorem NormalPrincipalListRank_all_acc
    (ps : NormalPrincipalListRank) :
    Acc NormalPrincipalListRank_lt ps := by
  sorry


-- -------------------------------------------------------------------------------
-- 11. Well-foundedness
-- -------------------------------------------------------------------------------

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
