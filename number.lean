import tidy.tidy
import tidy.rwing
import tactic.ring

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