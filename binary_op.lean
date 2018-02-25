import data.quot

import tidy.tidy

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
structure liftable_bop := mk ::
    {α : Type}
    (s : setoid α)
    (bop : bop α)
    (class_invar : bop_rel_invar s.r bop)

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

lemma lift_well_defined {α : Type} (s : setoid α) (γ : bop α) (class_invar : bop_rel_invar s.r γ)
: ∀ (a b c d : α), a ≈ c → b ≈ d → induced_quobop s γ a b = induced_quobop s γ c d :=
begin
    intros a b c d hac hbd,
    tidy,
    unfold bop_rel_invar at class_invar,
    specialize class_invar a b c d hac hbd,
    unfold induced_quobop,
    apply quot.sound,
    assumption,
end

def induced_bop {α : Type} (s : setoid α) (γ : bop α)
    (class_invar : bop_rel_invar s.r γ) : bop (quotient s)
:= quotient.lift₂ (induced_quobop s γ) (lift_well_defined s γ class_invar)

def lift_bop (lb : liftable_bop) : bop (quotient lb.s)
:= induced_bop lb.s lb.bop lb.class_invar

theorem compute_lift (lb : liftable_bop):
∀ a b : lb.α, (lift_bop lb) (quot.mk lb.s.r a) (quot.mk lb.s.r b) = quot.mk lb.s.r (lb.bop a b) := by tidy

--FIXME a single tactic should solve both of these below

lemma lift_assoc (lb : liftable_bop) : bop_rel_assoc lb.s.r lb.bop → bop_assoc (lift_bop lb) :=
begin
    intros hassoc a b c,
    -- unfold bop_assoc,
    -- unfold bop_rel_assoc at *,
    have haw : quot.mk lb.s.r (quot.out a) = a, by apply quotient.out_eq,
    have hbw : quot.mk lb.s.r (quot.out b) = b, by apply quotient.out_eq,
    have hcw : quot.mk lb.s.r (quot.out c) = c, by apply quotient.out_eq,
    rw eq.symm haw,
    rw eq.symm hbw,
    rw eq.symm hcw,
    rewrite (compute_lift lb (quot.out a) (quot.out b)),
    rewrite (compute_lift lb (quot.out b) (quot.out c)),
    rewrite (compute_lift lb (lb.bop (quot.out a) (quot.out b)) (quot.out c)),
    rewrite (compute_lift lb (quot.out a) (lb.bop (quot.out b) (quot.out c))),
    apply quot.sound,
    exact hassoc (quot.out a) (quot.out b) (quot.out c),
end

lemma lift_comm (lb : liftable_bop) : bop_rel_comm lb.s.r lb.bop → bop_comm (lift_bop lb) :=
begin
    intros hcomm a b,
    -- unfold bop_comm,
    -- unfold bop_rel_comm at *,
    have haw : quot.mk lb.s.r (quot.out a) = a, by apply quotient.out_eq,
    have hbw : quot.mk lb.s.r (quot.out b) = b, by apply quotient.out_eq,
    rw eq.symm haw,
    rw eq.symm hbw,
    rewrite (compute_lift lb (quot.out a) (quot.out b)),
    rewrite (compute_lift lb (quot.out b) (quot.out a)),
    apply quot.sound,
    exact hcomm (quot.out a) (quot.out b),
end