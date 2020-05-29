import data.real.basic

-- BEGIN
lemma my_lemma : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
begin
  intros x y ε epos ele1 xlt ylt,
  calc
    abs (x * y) = abs x * abs y : sorry
    ... ≤ abs x * ε             : sorry
    ... < 1 * ε                 : sorry
    ... = ε                     : sorry
end
-- END