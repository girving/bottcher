import Bottcher.Pray
import Interval.Approx.NormSq
import Ray.Dynamics.Mandelbrot
import Ray.Dynamics.Multibrot.Area
import Series.Series.Dyadic
import Series.Series.Rat
import Series.Series.Sum

/-!
# Upper bounds on the area of the Mandelbrot set
-/

open MeasureTheory (volume)
open scoped Real

variable {n : ℕ}
local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

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

variable {α : Type} [SeriesScalar α] [ApproxSeries α ℝ] [ApproxSeries α ℂ] [Div2 α] [ApproxDiv2 α ℂ]
  [NormSq α] [ApproxNormSq α ℂ]

/-- Series approximation of `upper` -/
def supper (n : ℕ) : α :=
  (spray n).sum fun k (x : α) ↦ (1 - k) * NormSq.normSq x

/-- `supper n` approximates `upper n` -/
lemma approx_supper (n : ℕ) : approx (supper n : α) (upper n) := by
  apply Series.approx_sum (g' := fun k x ↦ (1 - k) * ‖x‖ ^ 2)
  · approx
  · simp
  · simp
  · approx

/-- Specialisation to the dyadic rational case -/
lemma area_mandelbrot_le_supper (n0 : n ≠ 0) :
    volume.real mandelbrot ≤ π * (supper n : Dyadic).toRat := by
  have e := approx_supper n (α := Dyadic)
  simp only [approx] at e
  simp only [e, area_mandelbrot_le_upper n0]
