import Mathlib

--===============================================================================
-- Definition
--===============================================================================
/-
We follow Fernandez-Duque and Weiermann's notations. We represent the parameterized
collapsing function θ_X(ζ) as ψ(ζ) := θ_P(ζ) where P = {ω^{α} : α ∈ On}, the class
of principal ordinals (this does not lose any generality).
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
  cases h with
  | psi_forward h1 _ => exact omegaTerm_lt_irrefl h1
  | psi_reverse_lt h2 _ _ => exact omegaTerm_lt_irrefl h2
  | psi_reverse_eq h3 _ _ => exact omegaTerm_lt_irrefl h3
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
theorem principalList_tri (as bs : List principal) : principalList_lt as bs ∨ principalList_eq as bs ∨
                                                     principalList_lt bs as := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => exact Or.inr (Or.inl principalList_eq.nil)
    | cons b btail => exact Or.inl principalList_lt.nil
  | cons a atail ih =>
    cases bs with
    | nil => exact Or.inr (Or.inr principalList_lt.nil)
    | cons B Btail =>
      cases principal_tri a B with
      | inl hab => exact Or.inl (principalList_lt.head hab)
      | inr hrest =>
        cases hrest with
        | inl heq =>
          cases ih Btail with
          | inl htail => exact Or.inl (principalList_lt.tail heq htail)
          | inr htailrest =>
            cases htailrest with
            | inl htaileq => exact Or.inr (Or.inl (principalList_eq.cons heq htaileq))
            | inr htailrev => exact Or.inr (Or.inr (principalList_lt.tail (principal_eq_sym heq)
                                htailrev))
        | inr hba => exact Or.inr (Or.inr (principalList_lt.head hba))

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
                | inr hc32 => exact Or.inr (Or.inr (omegaTerm_lt.remainder (omegaTerm_eq_sym h23eq) (countableOrd_eq_sym hbeq) hc32))
            | inr hb3b2 => exact Or.inr (Or.inr (omegaTerm_lt.coefficient (omegaTerm_eq_sym h23eq) hb3b2))
        | inr ha3a2 => exact Or.inr (Or.inr (omegaTerm_lt.exponent ha3a2))
theorem coefficientList_tri (cs : List countableOrd) (bound : countableOrd) :
    coefficientList_lt cs bound ∨ ∃ c, c ∈ cs ∧ (bound <c c ∨ bound =c c) := by
  induction cs with
  | nil => left; exact coefficientList_lt.nil
  | cons c cs ih =>
    cases countableOrd_tri bound c with
    | inl hbc => right; exact ⟨c, List.mem_cons_self, Or.inl hbc⟩
    | inr hrest =>
      cases hrest with
      | inl heq => right; exact ⟨c, List.mem_cons_self, Or.inr heq⟩
      | inr hcb =>
        cases ih with
        | inl htail => left; exact coefficientList_lt.cons hcb htail
        | inr hexists =>
          cases hexists with
          | intro d hd =>
             cases hd with
            | intro hd_mem hd_rel => right; exact ⟨d, List.mem_cons_of_mem c hd_mem, hd_rel⟩

end
