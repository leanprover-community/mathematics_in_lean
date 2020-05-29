import tactic

open_locale classical

variable (Q : Prop)

-- BEGIN
example (h : ¬ ¬ Q) : Q :=
sorry

example (h : Q) : ¬ ¬ Q :=
sorry
-- END