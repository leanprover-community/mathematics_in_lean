import data.set.function tactic

open set function

variables {α β : Type*} [inhabited α]

noncomputable theory
open_locale classical

def inverse (f : α → β) : β → α :=
λ y : β, if h : ∃ x, f x = y then classical.some h else default α

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
  f (inverse f y) = y :=
begin
  rw inverse, dsimp, rw dif_pos h,
  exact classical.some_spec h
end

-- BEGIN
variable  f : α → β

example : injective f ↔ left_inverse (inverse f) f  :=
sorry

example : surjective f ↔ right_inverse (inverse f) f :=
sorry
-- END