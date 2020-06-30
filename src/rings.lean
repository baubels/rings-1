/-
Making some ring definitions in a lean
-/

import tactic

namespace myring

-- There are many many types of rings, might be annoying to add them all

-- my rings!
class ring (R : Type) extends has_add R, has_zero R, has_inv R, has_mul R, has_one R, has_neg R:=
(add_comm   : ∀ (a b : R), a + b = b + a)
(add_ass    : ∀ (a b c : R), (a + b) + c = a + (b + c))
(zero_add   : ∀ (a : R), 0 + a = a)
(add_zero   : ∀ (a : R), a + 0 = a)                         --prefer
(inv_add    : ∀ (a : R), (-a) + a = 0)
(add_inv    : ∀ (a : R), a + (-a) = 0)                      --prefer
(mul_ass    : ∀ (a b c : R), (a * b) * c = a * (b * c))
(left_dist  : ∀ (a b c : R), a * (b + c) = a * b + a * c)
(right_dist : ∀ (a b c : R), (a + b) * c = a * c + b * c)

/-
class comm_ring (R : Type) [ring R] :=
(M1 : ∀ (a b : R), a * b = b * a)

class unity_ring (R : Type) [ring R] :=
(M3l : ∀ (a : R), 1 * a = a)
(M3r : ∀ (a : R), a * 1 = a)

class no_zero_div_ring (R : Type) [ring R] :=
(Z : ∀ (a b : R), a * b = 0 → a = 0 ∨ b = 0)
-/

namespace ring 


variables {R : Type} [ring R]

-- I am so bad at this so I will do the most stupid of exercises
lemma add_is_comm {a b : R} : a + b = b + a :=
begin
  rw add_comm,
end

lemma add_is_comm' {a b : R} : a + b = b + a := by rw add_comm a b

lemma add_inv_add {a : R} : a + (-a) + a = a :=
begin 
    rw add_inv,
    rw zero_add,
end

lemma add_inv_add' {a : R} : a + (-a) + a = a :=
begin 
    rw [add_inv,zero_add],
end

lemma add_inv_add'' {a : R} : a + (-a) + a = a := by rw [add_inv,zero_add]
-- I think this is the shortest I can do

-- maybe with my little simp?

attribute [simp] add_inv zero_add

lemma add_inv_add''' {a : R} : a + (-a) + a = a := by simp
-- ok that is good


-- I wonder if we can just use right inverses/zeros instead of both
-- I think we definitely can, eg:
lemma add_inv_add'''' {a : R} : a + (-a) + a = a := 
begin 
    rw add_ass,
    rw inv_add,
    rw add_zero,
end

lemma add_inv_add''''' {a : R} : a + (-a) + a = a := by rw [add_ass, inv_add, add_zero]
-- ok

--can simpy do it?
attribute [simp] add_ass inv_add add_zero
lemma add_inv_add'''''' {a : R} : a + (-a) + a = a := by simp
-- ok, nice one

lemma many_adders {a : R} : a + (-a) + (-a) + a + (-a) + (-a) + a + a = 0 := by simp
-- ok



lemma zero_add1 {a : R} : 0 + a + 0 + a = a + a := 
begin 
    rw add_zero, 
    rw add_comm,
    rw ← add_ass,
    rw add_zero,
    /- 
    I had a bit of trouble being able to move around my cursor
    I could use simp, but being able to place my finger somewhere would be great
    Asking on zulip!
    -/
end

lemma add_left_cancel (a b c : R) (h: a + b = a + c) : b = c :=
begin 
calc b = 0 + b          : by rw zero_add
...    = ((-a) + a) + b : by rw inv_add
...    = (-a) + (a + b) : by rw add_ass
...    = (-a) + (a + c) : by rw h
...    = ((-a) + a) + c : by rw add_ass
...    = 0 + c          : by rw inv_add
...    = c              : by rw zero_add
end

-- can our simp do it?
attribute [simp] inv_add add_ass zero_add

-- first let's see where it stops doing its thing
lemma add_left_cancel' (a b c : R) (h: a + b = a + c) : b = c :=
begin
    rw ← zero_add b,
    rw ← inv_add a,
    rw add_ass,
    rw h,
    rw ← add_ass,
    rw inv_add,
    rw zero_add,
end

lemma add_left_cancel'' {a b c : R} (h: a + b = a + c) : b = c :=
begin
    rw ← zero_add b,
    rw ← inv_add a,
    rw add_ass,
    rw h,
    rw ← add_ass,
    rw inv_add,
    simp,
end

lemma add_left_cancel''' {a b c : R} (h: a + b = a + c) : b = c :=
begin
    rw ← zero_add b,
    rw ← inv_add a,
    rw add_ass,
    rw h,
    rw ← add_ass,
    simp,
end

-- nope so it can't do association, quite bad
lemma add_left_cancel'''' {a b c : R} (h: a + b = a + c) : b = c :=
begin
    rw ← zero_add b,
    rw ← inv_add a,
    rw add_ass,
    rw h,
    sorry
    --simp,
end

attribute [simp] inv_add add_ass zero_add add_comm

lemma add_left_cancel''''' {a b c : R} (h: a + b = a + c) : b = c :=
begin
    rw ← zero_add b,
    rw ← inv_add a,
    rw add_ass,
    rw h,
    simp [← add_ass],
end

lemma add_left_cancel'''''' {a b c : R} (h: a + b = a + c) : b = c :=
begin
    rw [←zero_add b, ←inv_add a, add_ass, h],
    simp [← add_ass],
end

--technically it's quicker like this
lemma add_left_cancel''''''' {a b c : R} (h: a + b = a + c) : b = c :=
    by rw [←zero_add b, ←inv_add a, add_ass, h, ←add_ass, inv_add, zero_add]

-- anyways, what's this all about:
lemma is_this_true {a : R} : a + a = 2 * a :=
begin
    -- why did changing input from {} to () let me use add_left_cancel?
    --rw ← add_zero (2*a), interesting not needed!
    apply add_left_cancel (-a),
    rw [←add_ass, inv_add, zero_add, add_comm],
    -- shit we need to show that -1*a is -a
    sorry
end

lemma right_multiply {a b c : R} (h: a = b) : a*c = b*c :=
begin 
    sorry --how do I get the property of the = sign?
end

theorem zero_multiply (a : R) : 0 * a = 0 :=
begin
    sorry
end

theorem multiply_zero (a : R) : a * 0 = 0 :=
begin
    sorry
end

end ring

end myring