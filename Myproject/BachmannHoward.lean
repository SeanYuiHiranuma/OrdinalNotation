import Mathlib

--===============================================================================
-- Definition
--===============================================================================
/-
Unlike the ordinals < ε₀ and < Γ₀, uncountable ordinals with the Ω-form "collapses"
into a countable form represented with the Veblen hierarchy. So, we define two
separate, although mutual, cases of (i) countable ordinals and (ii) uncountable
ordinals (technically, Ω-form term).
-/
mutual
inductive countableOrd where
  | sum : List cPrincipal → countableOrd
inductive cPrincipal where
  | phi : countableOrd → countableOrd → cPrincipal
  | psi : omegaTerm → cPrincipal
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
def ofPrincipal (p : cPrincipal) := sum [p] -- principal ordinal in terms of sum
def one : countableOrd := ofPrincipal (cPrincipal.phi zero zero)
def two : countableOrd := sum [(.phi zero zero), (.phi zero zero)]
def omega : countableOrd := ofPrincipal (.phi zero one)
def epsilonZero : countableOrd := ofPrincipal (.phi one zero)
end countableOrd

/-
As seen of the redunducy of the notation for zero (countableOrd.sum [] and omegaTerm.zero),
we embed countable ordinal notations into the omega term. Mathematically, any
countable ordinal β < Ω can be represented as Ω^{0}β + 0.
-/
namespace omegaTerm
def ofCountable : countableOrd → omegaTerm
| countableOrd.sum [] => omegaTerm.zero
| countableOrd.sum (p :: ps) => omegaTerm.omegaNF omegaTerm.zero
                                (countableOrd.sum (p :: ps)) omegaTerm.zero
def one : omegaTerm := ofCountable (countableOrd.one)
def two : omegaTerm := ofCountable (countableOrd.two)
def bigOmega : omegaTerm := omegaNF one countableOrd.zero zero

/-
As in Fernandez-Duque/Weiermann's paper, we define the function C(ζ) to retrieve
the coefficients of the Ω-form. Specifically, if ζ = Ω^{α}β + γ,
C(ζ) = C(α) ∪ C(γ) ∪ {β}
-/
def coefficients : omegaTerm → List countableOrd
  | zero => [countableOrd.zero]
  | omegaNF alpha beta gamma => (coefficients alpha) ++ (coefficients gamma) ++ [beta]
end omegaTerm



--===============================================================================
-- Comparison / Order
--===============================================================================
/-
The comparison between countables and φ_{α}(β) are simple. Pohler provides the following:
        φ_{α}(β) < φ_{γ}(δ) iff (i) α < γ and β < φ_{γ}(δ),
                                (ii) α = γ and β < δ
                                (iii) γ < α and φ_{α}(β) < δ
However, when we consider the ψ function, it becomes very complicated. We follow Fernandez-Duque/
Weiermann's notations for the explanation that follows. Given a parameterized collapsing function
Θ_X : ε_{Ω+1} → Ω, they introduce lemma 3.3.,
        If α < β < ε_{Ω+1}, then Θ_X(α) < Θ_X(β) iff α^* < Θ_X(β).
The collapsing function Θ_X(ζ) is defined to be the least θ ∈ X such that ζ^* < θ < Ω and for all
ζ < ξ, if ζ^* < θ then θ_X(ζ) < θ. ChatGPT puts this in very simple words: "θ_X(ζ)is the smallest
allowed countable ordinal above every coefficient of ξ, which is also closed above the collapses
of all earlier arguments whose coefficients fit below it." In this formalization ψ ≃ θ_X.
        ψ(α) < ψ (β) iff (i) α < β and α^* < ψ(β), or
                         (ii) β < α and ψ(α) ≤ β^*

-/

mutual
inductive countableOrd_lt : countableOrd → countableOrd → Prop where
  | sum {xs ys : List cPrincipal} (h : cPrincipalList_lt xs ys) :
        countableOrd_lt (countableOrd.sum xs) (countableOrd.sum ys)
inductive countableOrd_eq : countableOrd → countableOrd → Prop where
  | sum {xs ys : List cPrincipal} (h : cPrincipalList_eq xs ys) :
        countableOrd_eq (countableOrd.sum xs) (countableOrd.sum ys)
inductive cPrincipal_lt : cPrincipal → cPrincipal → Prop where
  -- The cases excluding ψ
  | phi_left {a b c d : countableOrd} (h1 : countableOrd_lt a c)
              (h2 : countableOrd_lt b (countableOrd.ofPrincipal (cPrincipal.phi c d))) :
              cPrincipal_lt (cPrincipal.phi a b) (cPrincipal.phi c d)
  | phi_eq {a b c d : countableOrd} (h1 : countableOrd_eq a c) (h2 : countableOrd_lt b d) :
              cPrincipal_lt (cPrincipal.phi a b) (cPrincipal.phi c d)
  | phi_right {a b c d : countableOrd} (h1 : countableOrd_lt c a)
              (h2 : countableOrd_lt (countableOrd.ofPrincipal (cPrincipal.phi a b)) d) :
              cPrincipal_lt (cPrincipal.phi a b) (cPrincipal.phi c d)
  -- The cases of comparing ψ(α) and ψ(β)
  | psi_forward {a b : omegaTerm} (h1 : omegaTerm_lt a b)
        (h2 : ∀c ∈ (omegaTerm.coefficients a), countableOrd_lt c (countableOrd.ofPrincipal (cPrincipal.psi b))) :
          cPrincipal_lt (cPrincipal.psi a) (cPrincipal.psi b)
  | psi_reverse {a b : omegaTerm} (h1 : omegaTerm_lt b a)
        (h2 : ∃ c ∈ omegaTerm.coefficients b,
        countableOrd_lt (countableOrd.ofPrincipal (cPrincipal.psi a)) c ∨
        countableOrd_eq (countableOrd.ofPrincipal (cPrincipal.psi a)) c) :
          cPrincipal_lt (cPrincipal.psi a) (cPrincipal.psi b)
  -- The cases of comparing φ_{α}(β) and ψ(γ)
inductive cPrincipal_eq : cPrincipal → cPrincipal → Prop where
  | phi {a b c d : countableOrd} (hac : countableOrd_eq a c) (hbd : countableOrd_eq b d) :
        cPrincipal_eq (cPrincipal.phi a b) (cPrincipal.phi c d)
  | psi {a b : omegaTerm} (hab : omegaTerm_eq a b) :
        cPrincipal_eq (cPrincipal.psi a) (cPrincipal.psi b)
inductive cPrincipalList_lt : List cPrincipal → List cPrincipal → Prop where
  | nil_cons {p : cPrincipal} {ps : List cPrincipal} : cPrincipalList_lt [] (p :: ps)
  | head {p q : cPrincipal} {ps qs : List cPrincipal} (h : cPrincipal_lt p q) :
          cPrincipalList_lt (p :: ps) (q :: qs)
  | tail {p q : cPrincipal} {ps qs : List cPrincipal} (h1 : cPrincipal_eq p q)
         (h2 : cPrincipalList_lt ps qs) : cPrincipalList_lt (p :: ps) (q :: qs)
inductive cPrincipalList_eq : List cPrincipal → List cPrincipal → Prop where
  | nil : cPrincipalList_eq [] []
  | cons {x y : cPrincipal} {xs ys : List cPrincipal} (h1 : cPrincipal_eq x y)
         (h2 : cPrincipalList_eq xs ys) : cPrincipalList_eq (x :: xs) (y :: ys)
inductive omegaTerm_lt : omegaTerm → omegaTerm → Prop where
inductive omegaTerm_eq : omegaTerm → omegaTerm → Prop where
  | zero : omegaTerm_eq omegaTerm.zero omegaTerm.zero
  -- Ω^{α}β+γ and Ω^{c}d+δ
  | omegaNF {a c gamma delta : omegaTerm} {b d : countableOrd} (h1 : omegaTerm_eq a c)
            (h2 : omegaTerm_eq gamma delta) (h3 : countableOrd_eq b d) :
            omegaTerm_eq (omegaTerm.omegaNF a b gamma) (omegaTerm.omegaNF c d delta)
end
