
structure order (α : Type) := mk ::
  (sim : α → α → Prop)
  (h_refl : ∀ a : α, sim a a)
  (h_antisymm : ∀ a b : α, sim a b ∧ sim b a → a = b)
  (h_trans : ∀ a b c : α, sim a b → sim b c → sim a b)

structure total_order (α : Type) extends order α := mk ::
  (h_total : ∀ a b : α, sim a b ∨ sim b a)