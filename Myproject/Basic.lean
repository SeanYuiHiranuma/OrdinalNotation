import Mathlib

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

#check mul_comm
#check mul_assoc
#check ℝ
#check 2+2

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c]
  rw [mul_assoc]
  rw [mul_comm a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
 rw [mul_assoc a b c]
 rw [h]
 rw [← mul_assoc a e f]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm b a]
  rw [sub_self]

section
variable (a b c : ℝ)
#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm
end

variable (a b c d : ℝ)
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [add_mul]
  rw [mul_add, mul_add]
  rw [mul_comm b a]
  rw [← add_assoc]
  rw [add_assoc (a * a) (a*b) (a*b)]
  rw [← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = (a*a+a*b)+(b*a+b*b) := by
      rw [add_mul, mul_add, mul_add]
    _ = (a*a+a*b+a*b)+b*b := by
      rw [← add_assoc, mul_comm b a]
    _ = a*a+(a*b+a*b)+b*b := by
      rw [add_assoc (a*a) (a*b) (a*b)]
    _ = a*a+2*(a*b)+b*b := by
      rw [← two_mul]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  calc
    (a+b)*(c+d) = a*c+a*d+(b*c+b*d) := by
      rw [add_mul, mul_add, mul_add]
    _ = a*c+a*d+b*c+b*d := by
      rw [← add_assoc]

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
#check add_comm a b

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 :=
  calc
    (a+b)*(a-b) = a*(a-b)+b*(a-b) := by
      rw [add_mul]
    _ = a*a-a*b+b*a-b*b := by
      rw [mul_sub a a b, mul_sub b a b, add_sub]
    _ = a*a-a*b+a*b-b*b := by
      rw [mul_comm b a]
    _ = a^2-a*b+a*b-b^2 := by
      rw [← pow_two a, ← pow_two b]
    _= a ^ 2 - b ^ 2 := by
      rw [sub_add_cancel]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
  (a+b)*(a+b) = a*(a+b)+b*(a+b) := by
    rw [add_mul]
  _ = (a*a+a*b)+(b*a+b*b) := by
    rw [mul_add, mul_add]
  _ = a*a+(a*b+(b*a+b*b)) := by
    rw [add_assoc]
  _ = a*a+(a*b+(a*b+b*b)) := by
    rw [mul_comm b a]
  _ = a*a+((a*b+a*b)+b*b) := by
    rw [← add_assoc (a*b) (a*b) (b*b)]
  _ = a*a+(2*(a*b)+b*b) := by
    rw [← two_mul (a*b)]
  _ = a * a + 2 * (a * b) + b * b := by
    rw [← add_assoc]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a+b)*(c+d) = (a*c+a*d)+(b*c+b*d) := by
      rw [add_mul, mul_add, mul_add]
    _ = ((a*c+a*d)+b*c)+b*d := by
      rw [← add_assoc (a*c+a*d) (b*c) (b*d)]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 :=
  calc
    (a+b)*(a-b) = a*(a-b)+b*(a-b) := by
      rw [add_mul]
    _ = (a*a-a*b)+(b*a-b*b) := by
      rw [mul_sub, mul_sub]
    _ = (a^2-a*b)+(b*a-b^2) := by
      rw [pow_two a, pow_two b]
    _ = (a^2-a*b)+((b*a+0)-b^2) := by
      rw [add_zero (b*a)]
    _ = (a^2-a*b)+(b*a+(0-b^2)) := by
      rw [← add_sub (b*a) 0 (b^2)]
    _ = (a^2-a*b)+b*a+(0-b^2) := by
      rw [← add_assoc (a^2-a*b) (b*a) (0-b^2)]
    _ = ((a^2+0)-a*b)+b*a+(0-b^2) := by
      rw [add_zero (a^2)]
    _ = (a^2+(0-a*b))+b*a+(0-b^2) := by
      rw [← add_sub (a^2) 0 (a*b)]
    _ = a^2+((0-a*b)+a*b)+(0-b^2) := by
      rw [add_assoc (a^2) (0-a*b) (b*a), mul_comm b a]
    _ = a^2+(0-b^2) := by
      rw [add_comm (0-a*b) (a*b), add_sub (a*b) 0 (a*b), add_zero (a*b), sub_self (a*b), add_zero (a^2)]
    _ = a^2-b^2 := by
      rw [add_sub, add_zero]

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a*d)] at hyp
  rw [← mul_assoc] at hyp
  exact hyp

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

theorem add_neg_cancel_right_practice (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_comm b (-b), neg_add_cancel, add_zero]

theorem add_left_cancel_practice {a b c : R} (h : a + b = a + c) : b = c :=
  calc
    b = b + 0 := by
      rw [add_zero b]
    _ = b + (-a + a) := by
      rw [← neg_add_cancel a]
    _ = b + (a+ -a) := by
      rw [add_comm (-a) a]
    _ = a+b+-a := by
      rw [← add_assoc, add_comm b a]
    _ = c+a+-a := by
      rw [h, add_comm a c]
    _ = c := by
      rw [add_assoc, add_neg_cancel a, add_zero]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0*a+0*a=0*a+0 := by
    rw [← add_mul, add_zero, add_zero]
  exact add_left_cancel h

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b :=
  calc
    -a = -a+0 := by
      rw [add_zero]
    _ = -a + a + b := by
      rw [←h, ← add_assoc]
    _ = 0+b := by
      rw [neg_add_cancel]
    _ = b := by
      rw [add_comm, add_zero]

theorem neg_neg_practice (a : R) : - -a = a :=
  calc
    - -a = - - a + 0 := by
      rw [add_zero (- - a)]
    _ = - - a + (-a + a) := by
      rw [neg_add_cancel]
    _ = 0 + a := by
      rw [← add_assoc, ← neg_add_cancel (-a)]
    _ = a := by
      rw [add_comm, add_zero]

theorem neg_add_cancel_left_practice (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_neg_cancel_right_practice2 (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_comm b (-b), neg_add_cancel, add_comm, zero_add]

#check add_zero

theorem add_right_cancel_practice {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_zero a, ← neg_add_cancel b, add_comm (-b) b, ← add_assoc, h, add_assoc, add_comm b (-b)]
  rw [neg_add_cancel, add_zero]

theorem zero_mul_practice (a : R) : 0 * a = 0 := by
  have h : 0*a+0*a=0*a+0 := by
    rw [← add_mul, add_zero 0, add_zero (0*a)]
  rw [add_left_cancel h]

theorem neg_eq_of_add_eq_zero_practice {a b : R} (h : a + b = 0) : -a = b := by
  rw [← add_zero (-a), ← h, ← add_assoc, neg_add_cancel, zero_add]

theorem eq_neg_of_add_eq_zero_practice {a b : R} (h : a + b = 0) : a = -b := by
  rw [← add_zero a, ← neg_add_cancel b, add_comm (-b) b, ← add_assoc, h, zero_add]

theorem neg_zero_practice : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg_practice2 (a : R) : - -a = a := by
  rw [← add_zero (- - a), ← neg_add_cancel a, ← add_assoc, neg_add_cancel (-a), zero_add]

example (a b : R) : a - b = a + -b :=
    sub_eq_add_neg a b

theorem self_sub (a : R) : a - a = 0 := by
  apply sub_eq_zero.mpr
  exact rfl

theorem two_mul_practice (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans -- x<=?m ?m<=z
  · apply h₀
  · apply h₁

variable (a b c d : ℝ)

example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt -- a<=?m  ?m<e
  · apply h₀ -- ?m = b
  · apply lt_trans -- b<?m ?m<e
    · apply h₁ -- ?m = c
    · apply lt_of_le_of_lt
      · apply h₂
      · apply h₃

example (h : a ≤ b) : Real.exp a ≤ Real.exp b := by
  rw [Real.exp_le_exp]
  exact h

variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

#check ∀ x : ℝ, 0 ≤ x → |x| = x

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

def predRel (m n : Nat) : Prop := m + 1 = n
#check predRel 2 3
theorem zeroIsAccessible : Acc predRel 0 := by
  apply Acc.intro -- goal becomes for all b with predRel b 0, b is accessible
  intro b hb -- take arbitrary b and assume predRel b 0
  unfold predRel at hb
  omega
theorem oneIsAccessible : Acc predRel 1 := by
  apply Acc.intro
  intro b hb -- hb = predRec b 1
  unfold predRel at hb -- hb = (b +1 = 1)
  have hb0 : b = 0 := by omega
  subst b
  exact zeroIsAccessible
theorem nIsAccessible : ∀ n : Nat, Acc predRel n := by
  intro n
  induction n with
    | zero => apply Acc.intro
              intro b hb -- predRel b 0
              unfold predRel at hb -- b + 1 = 0
              omega
    | succ n ih => apply Acc.intro
                   intro b hb -- pred b n+1
                   unfold predRel at hb -- b + 1 = n+1
                   have hbn : b = n := by omega
                   subst b
                   exact ih
/-
"WellFounded r" means every element is acessible with respect to r. (∀ a, Acc r a)
-/
theorem predRel_wf : WellFounded predRel := by
  constructor -- changes goal to ∀ n, Acc predRel n
  intro n
  induction n with
  | zero => exact zeroIsAccessible
  | succ n ih => apply Acc.intro
                 intro b hb
                 unfold predRel at hb
                 have hb_eq : b = n := by omega
                 subst b
                 exact ih



end
