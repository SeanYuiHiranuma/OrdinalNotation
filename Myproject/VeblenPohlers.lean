import Mathlib

inductive vOT where
  | vnf : List (vOT × vOT) → vOT

/-
Ordinals below Γ₀ can be represented in a normal form as
  α = φ_{ζ₁}(η₁) + ... + φ_{ζₙ}(ηₙ)
In this ordinal notation, we want to represent this by
picking up the two variables ζᵢ and ηᵢ.
-/

namespace vOT
def zero : vOT := vOT.vnf []
def one : vOT := vOT.vnf [(zero, zero)]
def omega : vOT := vOT.vnf [(zero, one)]
def epsilon_zero : vOT := vOT.vnf [(one, zero)]


-- COMPARISON LAW
/-
The comparison we define here would be a bit more complicated
than the lexicographic definition for ordinals below ε₀.
      Denote P := φ_{α}(β) and Q := φ_{γ}(δ)
Using Theorem 3.4.8 of Pohlers, we have the following relation
P < Q iff (i) α < γ and β < Q
          (ii) α = γ and β < δ
          (iii) γ < α and P < δ
P = Q iff (i) α < γ and β = Q
          (ii) α = γ and β = δ
          (iii) γ < α and P = δ
We attempt to formalize this. Our general method is to consider four cases
  (i) Equivalence of principal (meaning just a singular φ_{α}(β))
  (ii) Comparison of principal
  (iii) Equivalence of vOT
  (iv) Comparison of vOT
  (v) Equivalence of List vOT
  (vi) Comparison of List vOT
-/

abbrev PT := vOT × vOT
def phi (a b : vOT) : vOT := vOT.vnf [(a, b)]

-- Strict comparison and equivalence
mutual
inductive vOT_lt : vOT → vOT → Prop where
  | vnf {xs ys : List PT} : vList_lt xs ys → vOT_lt (vOT.vnf xs) (vOT.vnf ys)
inductive vList_lt : List PT → List PT → Prop where
  | nil_cons {q : PT} {qs : List PT} : vList_lt [] (q :: qs)
  | head_lt {x y : PT} {xs ys : List PT} : vPT_lt x y → vList_lt (x :: xs) (y :: ys)
  | tail_lt {x y : PT} {xs ys : List PT} : vPT_equiv x y → vList_lt xs ys →
                                           vList_lt (x :: xs) (y :: ys)
inductive vPT_lt : PT → PT → Prop where
  | index_lt {a b c d : vOT} : vOT_lt a c → vOT_lt b (phi c d) → vPT_lt (a, b) (c, d)
  | index_equiv {a b c d : vOT} : vOT_equiv a c → vOT_lt b d → vPT_lt (a, b) (c, d)
  | index_gt {a b c d : vOT} : vOT_lt c a → vOT_lt (phi a b) d → vPT_lt (a, b) (c, d)
inductive vOT_equiv : vOT → vOT → Prop where
  | vnf {xs ys : List PT} : vList_equiv xs ys → vOT_equiv (vOT.vnf xs) (vOT.vnf ys)
inductive vPT_equiv : PT → PT → Prop where
  | index_lt {a b c d : vOT} : vOT_lt a c → vOT_lt b (phi c d) → vPT_equiv (a, b) (c, d)
  | index_equiv {a b c d : vOT} : vOT_equiv a c → vOT_equiv b d → vPT_equiv (a, b) (c, d)
  | index_gt {a b c d : vOT} : vOT_lt c a → vOT_equiv (phi a b) d → vPT_equiv (a, b) (c, d)
inductive vList_equiv : List PT → List PT → Prop where
  | nil : vList_equiv [] []
  | cons {x y : PT} {xs ys : List PT} : vPT_equiv x y → vList_equiv xs ys
                                      → vList_equiv (x :: xs) (y :: ys)
end
infix:50 " ≺ᵥ " => vOT_lt
infix:50 " =ᵥ " => vOT_equiv
-- Non-strict comparison of principals
def vPT_le (x y : PT) : Prop := vPT_lt x y ∨ vPT_equiv x y


-- NORMALITY
/-
Given the construction of the normal form of ordinals below Γ₀, the representation
        α = φ_{a₁}(b₁) + φ_{a₂}(b₂) + ... + φ_{aₙ}(bₙ)
must satisfy φ_{a₁}(b₁) ≥ φ_{a₂}(b₂) ≥ ... ≥ φ_{aₙ}(bₙ).
-/
mutual
inductive normal : vOT → Prop where
  | vnf {xs : List PT} : normalList xs → normal (vOT.vnf xs)
inductive normalList : List PT → Prop where
  | nil : normalList []
  | singleton {x : PT} : normalPT x → normalList [x]
  | cons {x y : PT} {xs : List PT} : normalPT x → vPT_le y x → normalList (y :: xs)
                                   → normalList (x :: y :: xs)
inductive normalPT : PT → Prop where
  | cons {a b : vOT} : normal a → normal b → normalPT (a, b)
end




end vOT
