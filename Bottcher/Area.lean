import Bottcher.Dyadic
import Bottcher.NormSq
import Bottcher.Pray
import Bottcher.Rat
import Ray.Dynamics.Mandelbrot
import Ray.Dynamics.Multibrot.Area

/-!
# Upper bounds on the area of the Mandelbrot set
-/

open MeasureTheory (volume)
open scoped Real

variable {n : ℕ}
local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩
variable {α : Type} [SeriesScalar α] [ApproxSeries α ℂ] [Div2 α] [ApproxDiv2 α ℂ] [NormSq α]
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-!
### Mandelbrot area upper bound, in rational form
-/

/-- Our area upper bound divided by `π` so that it is rational -/
noncomputable def upper (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (1 - k) * ‖series_coeff k (pray 2) 0‖ ^ 2

/-- `π * upper n` is a Mandelbrot area upper bound -/
lemma area_mandelbrot_le_upper (n0 : n ≠ 0) : volume.real mandelbrot ≤ π * upper n := by
  rw [mandelbrot_eq_multibrot]
  induction' n with n h
  · simp at n0
  · refine le_trans (multibrot_volume_le (Finset.range n)) (le_of_eq ?_)
    simp only [upper, Finset.sum_range_succ', series_coeff_zero', pray_zero, Nat.cast_zero,
      sub_zero, norm_one, one_pow, mul_add, mul_one, Nat.cast_add_one,
      sub_add_cancel_right, neg_mul, Finset.sum_neg_distrib, mul_neg, Finset.mul_sum, ← mul_assoc]
    ring_nf
    simp only [series_coeff, smul_eq_mul, mul_comm]

/-!
### Series approximation of `upper`
-/

/-- Series approximation of `upper` -/
def supper (n : ℕ) : α :=
  ((spray n).c.mapIdx fun k (x : α) ↦ (1 - k) * NormSq.normSq x).sum
