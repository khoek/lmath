import tidy.tidy
import tidy.rwing
import tactic.ring

--prereqs

lemma diff_zero {a b : ℤ} : a - b = 0 → a = b :=
begin
    intro h1,
    have h2 : a = a - b + b,
    rwing [h2, h1],
end

theorem cancellation_law {a b c : ℤ} (h : a ≠ 0) : a * b = a * c → b = c := 
begin
    intro h1,
    have h2 : a * (b - c) = 0, by rwing h1,
    have h3 : a = 0 ∨ b - c = 0, from eq_zero_or_eq_zero_of_mul_eq_zero h2,
    apply diff_zero (or.resolve_right (or.symm h3) h),
end

theorem zero_prod {a b : ℤ} (h : a = 0 ∨ b = 0) : a * b = 0 :=
begin
    by_cases hc : a = 0,
    rwing hc,
    have hs : b = 0,
    exact (or.resolve_left h hc),
    rwing hs,
end

theorem nonzero_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
begin
    by_contradiction hc,
    simp at hc,
    have hm : a = 0 ∨ b = 0, by exact (eq_zero_or_eq_zero_of_mul_eq_zero hc),
    obviously,
end

--begin lib

-- lemma quot_equiv (α : Type) (β : setoid α) ( a b : α )
--     : (β.r a b) ↔ quot.mk β.r a = quot.mk β.r b :=
-- begin
--     intros a b,
--     tidy,
--     apply quot.sound,
--     tidy,
--     apply (quotient.exact a_1),
-- end

lemma eq_is_refl {α : Type} {r : α → α → Prop} : equivalence r → reflexive r
:= by intro h; exact and.elim_left h
lemma eq_is_symm {α : Type} {r : α → α → Prop} : equivalence r → symmetric r
:= by intro h; exact and.elim_left (and.elim_right h)
lemma eq_is_trans {α : Type} {r : α → α → Prop} : equivalence r → transitive r := by intro h; exact and.elim_right (and.elim_right h)

def bop (α : Type) := α → α → α
def prebop (α β : Type) := α → α → β

def bop_rel_assoc {α : Type} (r : α → α → Prop) (γ : bop α)
:= ∀ a b c : α, r (γ (γ a b) c) (γ a (γ b c))
def bop_rel_comm {α : Type} (r : α → α → Prop) (γ : bop α)
:= ∀ a b : α, r (γ a b) (γ b a)

def bop_assoc {α : Type} (γ : bop α) := bop_rel_assoc eq γ
def bop_comm {α : Type} (γ : bop α) := bop_rel_comm eq γ

def bop_rel_invar_first {α : Type} (r : α → α → Prop) (γ : bop α)
:= ∀ a b c : α, r a b → r (γ a c) (γ b c)
def bop_rel_invar {α : Type} (r : α → α → Prop) (γ : bop α)
:= ∀ a b c d : α, r a c → r b d → r (γ a b) (γ c d)

lemma bop_comm_easy_invar {α : Type} {s : setoid α} {γ : bop α} : bop_rel_comm s.r γ → bop_rel_invar_first s.r γ → bop_rel_invar s.r γ :=
begin
    have htrans : transitive s.r, by exact eq_is_trans s.iseqv,
    have hsymm : symmetric s.r, by exact eq_is_symm s.iseqv,
    intros hcomm hfirst,
    unfold bop_rel_comm at *,
    unfold bop_rel_invar_first at *,
    unfold bop_rel_invar at *,
    intros a b c d hac hbd,
    apply htrans,
    apply hfirst a c b hac,
    apply htrans,
    apply hcomm c b,
    apply hsymm,
    apply htrans,
    apply hcomm c d,
    exact hfirst d b c (hsymm hbd),
end

def induced_quobop {α : Type} (s : setoid α) (γ : bop α) : prebop α (quotient s)
:= λ a b : α, quot.mk s.r (γ a b)
def induced_bop {α : Type} (s : setoid α) (γ : bop α)
    (class_invar : bop_rel_invar s.r γ) : bop (quotient s) :=
begin
    apply quotient.lift₂ (induced_quobop s γ),
    intros a b c d h1 h2,
    tidy,
    unfold bop_rel_invar at class_invar,
    specialize class_invar a b c d h1 h2,
    unfold induced_quobop,
    apply quot.sound,
    assumption,
end

lemma lift_comm {α : Type} {s : setoid α} {γ : bop α}
    {class_invar : bop_rel_invar s.r γ} (induced_bop s γ class_invar : bop (quotient s))
    : bop (quotient s) :=
begin
    unfold bop_comm,
    admit
end

--begin rat construction

structure pair := mk ::
  ( x y : ℤ )
  ( non_zero : y ≠ 0)

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

def pair_add : bop pair :=
    assume a b : pair,
    have hnz : a.2 * b.2 ≠ 0, from nonzero_mul a.non_zero b.non_zero,
    pair.mk (a.1 * b.2 + b.1 * a.2) (a.2 * b.2) hnz

def pair_mul : bop pair :=
    assume a b : pair,
    have hnz : a.2 * b.2 ≠ 0, from nonzero_mul a.non_zero b.non_zero,
    pair.mk (a.1 * b.1) (a.2 * b.2) hnz

--proving of the operations

lemma pair_add_comm : bop_rel_comm q_law pair_add
:= by intros a b; unfold q_law; obviously
lemma pair_mul_comm : bop_rel_comm q_law pair_mul
:= by intros a b; unfold q_law; obviously

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

-- rational operations

def rat_add : bop ℚℚ := induced_bop pair_setoid pair_add pair_add_invar
def rat_mul : bop ℚℚ := induced_bop pair_setoid pair_mul pair_mul_invar

theorem compute_rat_add : ∀ a b : pair, rat_add (ℚℚ.mk a) (ℚℚ.mk b) = ℚℚ.mk (pair_add a b) := by tidy
theorem compute_rat_mul : ∀ a b : pair, rat_mul (ℚℚ.mk a) (ℚℚ.mk b) = ℚℚ.mk (pair_mul a b) := by tidy

def rat_add_comm : bop_comm rat_add := sorry
def rat_mul_comm : bop_comm rat_mul := sorry

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

--examples

def pair_add_rat_direct : pair → pair → ℚℚ
:= λ a b : pair, (ℚℚ.mk (pair_add a b))
example : ∀ a b : pair, pair_add_rat_direct a b = (induced_quobop pair pair_setoid pair_add) a b := by tidy

#check q_law