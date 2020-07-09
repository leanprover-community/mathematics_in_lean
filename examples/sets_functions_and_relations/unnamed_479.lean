import data.nat.prime data.nat.parity tactic

open set nat

example : { n | prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
sorry