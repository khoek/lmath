import tidy.tidy
import tidy.rwing
import tactic.ring

--prereqs

lemma diff_zero {a b : ℤ} : a - b = 0 → a = b :=
begin
    intro h1,
    have h2 : a = a - b + b,
    rwing [h2, h1],
-- calc a = (a - b) + b : by ring
--    ... = b           : by rw h1; simp
end

theorem cancellation_law {a b c : ℤ} (h : a ≠ 0) : a * b = a * c → b = c := 
begin
    intro h1,
    -- have h2 : a * (b - c) = 0, from calc
    --     a * (b - c) = a * b - a * c : by ring
    --             ... = a * b - a * b : by rw h1
    --             ... = 0 : by ring,
    have h2 : a * (b - c) = 0, by rwing h1,
    have h3 : a = 0 ∨ b - c = 0, from eq_zero_or_eq_zero_of_mul_eq_zero h2,
    apply diff_zero (or.resolve_right (or.symm h3) h),
end

theorem zero_prod {a b : ℤ} (h : a = 0 ∨ b = 0) : a * b = 0 :=
begin
    by_cases hc : a = 0,
    rewrite hc,
    ring,
    have hs : b = 0,
    exact (or.resolve_left h hc),
    rwing hs,
end

theorem nonzero_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
begin
    by_contradiction hc,
    have hm : a * b = 0,
    by tidy,
    have ho : a = 0 ∨ b = 0,
    apply eq_zero_or_eq_zero_of_mul_eq_zero,
    exact hm,
    have hn1 : a ≠ 0 ∧ b ≠ 0,
    exact and.intro ha hb,
    have hn2 : ¬(a = 0 ∨ b = 0),
    by obviously,
    contradiction,
end

--begin

structure pair := mk ::
  ( x y : ℤ )
  ( non_zero : y ≠ 0)

def pair_add : pair → pair → pair :=
    assume a b : pair,
    have hnz : a.2 * b.2 ≠ 0, from nonzero_mul a.non_zero b.non_zero,
    pair.mk (a.1 * b.2 + b.1 * a.2) (a.2 * b.2) hnz

def pair_mul : pair → pair → pair :=
    assume a b : pair,
    have hnz : a.2 * b.2 ≠ 0, from nonzero_mul a.non_zero b.non_zero,
    pair.mk (a.1 * b.1) (a.2 * b.2) hnz

def q_law : pair → pair → Prop := λ a b : pair, a.1 * b.2 = b.1 * a.2

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

theorem q_refl : ∀ ( a : pair ), q_law a a := begin
    assume a : pair,
    show q_law a a, from rfl
end

theorem q_symm : ∀ ( a b : pair ), q_law a b → q_law b a :=
    assume a b : pair,
    assume h : q_law a b,
    show q_law b a, from eq.symm h

instance pair_setoid := setoid.mk q_law (mk_equivalence q_law q_refl q_symm q_trans)

def ℚℚ := quotient pair_setoid
def ℚℚ.mk (p : pair) : ℚℚ := quot.mk q_law p
def ℚℚ.divide (a b : ℤ) (h : b ≠ 0) : ℚℚ := ℚℚ.mk (pair.mk a b h)
def ℚℚ.from_int (n : ℤ) : ℚℚ := ℚℚ.mk (pair.mk n 1 one_ne_zero)

lemma pair_equiv :  ∀ ( a b : pair ), q_law a b ↔ ℚℚ.mk a = ℚℚ.mk b :=
begin
    tidy,
    apply quot.sound,
    tidy,
    apply (quotient.exact a_1),
end

def pair_add_rat : pair → pair → ℚℚ := λ a b : pair, (ℚℚ.mk (pair_add a b))
def pair_mul_rat : pair → pair → ℚℚ := λ a b : pair, (ℚℚ.mk (pair_mul a b))

lemma pair_add_comm : ∀ a b : pair, pair_add_rat a b = pair_add_rat b a := 
begin
   intros a b,
   unfold pair_add_rat,
   apply iff.mp (pair_equiv (pair_add a b) (pair_add b a)),
   unfold q_law,
   obviously,
end

lemma pair_add_invar_sub : ∀ a b c : pair, q_law a b → pair_add_rat a c = pair_add_rat b c :=
begin
   intros a b c h,
   unfold pair_add_rat,
   apply iff.mp (pair_equiv (pair_add a c) (pair_add b c)),
   unfold q_law,
   unfold pair_add,
   simp,
   ring,
   have h : a.x * b.y = b.x * a.y,
   obviously,
end

lemma pair_add_invar : ∀ a c b d : pair, a ≈ b → c ≈ d → pair_add_rat a c = pair_add_rat b d :=
begin
   intros a c b d,
   dsimp_all',
   intros h1 h2,
   apply eq.trans (pair_add_invar_sub a b c h1),
   apply eq.trans (pair_add_comm b c),
   symmetry,
   apply eq.trans (pair_add_comm b d),
   apply pair_add_invar_sub,
   apply q_symm,
   exact h2,
end

lemma pair_mul_comm : ∀ a b : pair, pair_mul_rat a b = pair_mul_rat b a := 
begin
   intros a b,
   unfold pair_mul_rat,
   apply iff.mp (pair_equiv (pair_mul a b) (pair_mul b a)),
   unfold q_law,
   obviously,
end

lemma pair_mul_invar_sub : ∀ a b c : pair, q_law a b → pair_mul_rat a c = pair_mul_rat b c :=
begin
   intros a b c h,
   unfold pair_mul_rat,
   apply iff.mp (pair_equiv (pair_mul a c) (pair_mul b c)),
   unfold q_law,
   have hh : a.x * b.y = b.x * a.y,
   by apply h,
   obviously,
end

lemma pair_mul_invar : ∀ a c b d : pair, a ≈ b → c ≈ d → pair_mul_rat a c = pair_mul_rat b d :=
begin
   intros a c b d,
   dsimp_all',
   intros h1 h2,
   apply eq.trans (pair_mul_invar_sub a b c h1),
   apply eq.trans (pair_mul_comm b c),
   symmetry,
   apply eq.trans (pair_mul_comm b d),
   apply pair_mul_invar_sub,
   apply q_symm,
   exact h2,
end

-- rational operators

def rat_add : ℚℚ → ℚℚ → ℚℚ := quotient.lift₂ pair_add_rat pair_add_invar
def rat_mul : ℚℚ → ℚℚ → ℚℚ := quotient.lift₂ pair_mul_rat pair_mul_invar

theorem compute_rat_add : ∀ a b : pair, rat_add (ℚℚ.mk a) (ℚℚ.mk b) = ℚℚ.mk (pair_add a b) := by tidy
theorem compute_rat_mul : ∀ a b : pair, rat_mul (ℚℚ.mk a) (ℚℚ.mk b) = ℚℚ.mk (pair_mul a b) := by tidy

theorem rat_add_comm : ∀ a b : ℚℚ, rat_add a b = rat_add b a :=
begin
    intros a b,
    have haw : ℚℚ.mk (quot.out a) = a,
    apply quotient.out_eq,
    have hbw : ℚℚ.mk (quot.out b) = b,
    apply quotient.out_eq,
    rw eq.symm haw,
    rw eq.symm hbw,
    apply pair_add_comm,
end

theorem rat_mul_comm : ∀ a b : ℚℚ, rat_mul a b = rat_mul b a :=
begin
    intros a b,
    have haw : ℚℚ.mk (quot.out a) = a,
    apply quotient.out_eq,
    have hbw : ℚℚ.mk (quot.out b) = b,
    apply quotient.out_eq,
    rw eq.symm haw,
    rw eq.symm hbw,
    apply pair_mul_comm,
end

#check q_law