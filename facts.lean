--facts which should be in the library but I haven't been bothered to find

lemma quotient_fact { β : Type } { α : setoid β } { a b : β } : (@setoid.r β α a b) → quot.mk α.r a = quot.mk α.r b := by admit
lemma leq_fact { a b : ℤ } : a ≤ b → b ≤ a → a = b := by admit