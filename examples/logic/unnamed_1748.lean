import data.real.basic
import data.nat.gcd

open nat

-- BEGIN
example (x y : ℝ) : abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
begin
  rw abs_lt,
  intro h,
  split; linarith
end

example : 3 ∣ gcd 6 15 :=
begin
  rw dvd_gcd_iff,
  split; norm_num
end
-- END