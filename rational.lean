import tidy.tidy
import tactic.ring

import .number
import .binary_op
import .order
import .facts

--define pairs and the rational equality law

structure pair := mk ::
  ( x y : ℤ )
  ( non_zero : y ≠ 0)

def q_law : pair → pair → Prop := λ a b : pair, a.1 * b.2 = b.1 * a.2

theorem q_refl : ∀ ( a : pair ), q_law a a
    := by unfold q_law; intro a; refl
theorem q_symm : ∀ ( a b : pair ), q_law a b → q_law b a
    := by unfold q_law; intros a b; tidy
theorem q_trans : ∀ (a b c : pair), (q_law a b) → (q_law b c) → (q_law a c) := begin
    intros a b c,
    unfold q_law,
    intros h1 h2,
    have hr : b.2 * (c.1 * a.2) = b.2 * (a.1 * c.2), from calc
        b.2 * (c.1 * a.2) = a.2 * (c.1 * b.2) : by ring
                    ... = a.2 * (b.1 * c.2) : by rw h2
                    ... = (b.1 * a.2) * c.2 : by ring
                    ... = (a.1 * b.2) * c.2 : by rw h1
                    ... = b.2 * (a.1 * c.2) : by ring,
    exact eq.symm (cancellation_law b.non_zero hr),
end

instance pair_setoid := setoid.mk q_law (mk_equivalence q_law q_refl q_symm q_trans)

def pair_add : bop pair
    := λ a b : pair, pair.mk (a.1 * b.2 + b.1 * a.2) (a.2 * b.2)
        (nonzero_mul a.non_zero b.non_zero)

def pair_mul : bop pair
    := λ a b : pair, pair.mk (a.1 * b.1) (a.2 * b.2)
        (nonzero_mul a.non_zero b.non_zero)

--proving well-definedness, and then commutativity

lemma pair_add_assoc : bop_rel_assoc q_law pair_add
    := by intros a b c; unfold q_law; unfold pair_add; simp; ring
lemma pair_mul_assoc : bop_rel_assoc q_law pair_mul
    := by intros a b c; unfold q_law; unfold pair_mul; simp; ring

lemma pair_add_comm : bop_rel_comm q_law pair_add
    := by intros a b; unfold q_law; unfold pair_add; simp; ring
lemma pair_mul_comm : bop_rel_comm q_law pair_mul
    := by intros a b; unfold q_law; unfold pair_mul; simp; ring

lemma pair_add_invar_first : bop_rel_invar_first q_law pair_add :=
begin
   intros a b c h,
   unfold q_law,
--FIXME these three lines are need because obviously is really slow without
   unfold pair_add,
   simp,
   ring,
   have hh : a.x * b.y = b.x * a.y, by apply h,
   obviously,
end

lemma pair_mul_invar_first : bop_rel_invar_first q_law pair_mul :=
begin
   intros a b c h,
   unfold q_law,
   have hh : a.x * b.y = b.x * a.y, by apply h,
   obviously,
end

lemma pair_add_invar : bop_rel_invar q_law pair_add
:= bop_comm_easy_invar pair_add_comm pair_add_invar_first
lemma pair_mul_invar : bop_rel_invar q_law pair_mul
:= bop_comm_easy_invar pair_mul_comm pair_mul_invar_first

def pair_add_l := liftable_bop.mk pair_setoid pair_add pair_add_invar
def pair_mul_l := liftable_bop.mk pair_setoid pair_mul pair_mul_invar

-- lift the above construction to give the rationals

def ℚℚ := quotient pair_setoid
def ℚℚ.mk (p : pair) : ℚℚ := quot.mk q_law p
def ℚℚ.divide (a b : ℤ) (h : b ≠ 0) : ℚℚ := ℚℚ.mk (pair.mk a b h)
def ℚℚ.from_int (n : ℤ) : ℚℚ := ℚℚ.mk (pair.mk n 1 one_ne_zero)

def rat_add : bop ℚℚ := lift_bop pair_add_l
def rat_mul : bop ℚℚ := lift_bop pair_mul_l

-- addition and multiplication are associative and commutative

theorem rat_add_assoc : bop_assoc rat_add
    := lift_assoc pair_add_l pair_add_assoc
theorem rat_add_comm : bop_comm rat_add
    := lift_comm pair_add_l pair_add_comm

theorem rat_mul_assoc : bop_assoc rat_mul
    := lift_assoc pair_mul_l pair_mul_assoc
theorem rat_mul_comm : bop_comm rat_mul
    := lift_comm pair_mul_l pair_mul_comm

--example of the equivalence of the general construction above to the ``direct way''

def pair_add_rat_direct : pair → pair → ℚℚ
:= λ a b : pair, (ℚℚ.mk (pair_add a b))
example : ∀ a b : pair, pair_add_rat_direct a b = (induced_quobop pair_setoid pair_add) a b := by tidy

--order

def rat_leq_rel (a b : ℚℚ) : Prop := (quot.out a).1 * (quot.out b).2 ≤ (quot.out b).1 * (quot.out a).2

lemma rat_req_refl : ∀ a : ℚℚ, rat_leq_rel a a := by unfold rat_leq_rel; tidy
lemma rat_req_antisymm : ∀ a b : ℚℚ, rat_leq_rel a b → rat_leq_rel b a → a = b :=
begin
    intros a b h1 h2,
    have hm : (quot.out b).x * (quot.out a).y = (quot.out a).x * (quot.out b).y,
        unfold rat_leq_rel at *,
        apply eq.symm (leq_fact h1 h2),
    clear h1 h2,
    have hn : ℚℚ.mk (quot.out a) = ℚℚ.mk (quot.out b),
        have hl : q_law (quot.out a) (quot.out b),
            unfold q_law,
            apply eq.symm hm,
        apply (@quotient_fact pair pair_setoid (quot.out a) (quot.out b)),
        exact hl,
    transitivity,
    apply eq.symm (quotient.out_eq a),
    transitivity,
    apply hn,
    apply quotient.out_eq,
end

#check quotient pair_setoid
#check @quotient.out_eq pair pair_setoid 

lemma rat_req_trans : ∀ a b c : ℚℚ, rat_leq_rel a b → rat_leq_rel b c → rat_leq_rel a c :=
begin
    intros a b c h1 h2,
    unfold rat_leq_rel at *,
    admit
end

#check rat_leq_rel

-- Scott: Why is this definition of rat_leq okay? Even though it secretly is, it
-- may not even be well-defined in the sense which I intend. I suppose the 
-- ``constructive'' interpretation is that there is some distinguished function 
-- quot.out : ℚℚ → pair which can reliably give the same element for each 
-- equivalence class. This is still very strange to me! Am I really just 
-- thinking that the Axiom of Choice is strange?