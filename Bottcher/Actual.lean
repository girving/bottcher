import Batteries.Data.Rat.Float
import Bottcher.Area
import Bottcher.Dyadic
import Bottcher.Pray
import Bottcher.Rat

/-!
# Actual computation of the Böttcher series for the Mandelbrot set
-/

open MeasureTheory (volume)
open scoped Real

/-- The first 10 terms -/
lemma spray_10 : (spray 10 : Series ℚ).c =
    #[1, -1/2, 1/8, -1/4, 15/128, 0, -47/1024, -1/16, 987/32768, 0] := by native_decide

-- More terms. Uncomment for fun!
-- #eval (spray 100 : Series Dyadic).c

/-- An upper bound on the area of the Mandelbrot set -/
lemma area_mandelbrot_le : volume.real mandelbrot ≤ 0.63006 * π := by
  refine le_trans (area_mandelbrot_le_supper (n := 256) (by norm_num)) ?_
  simp only [mul_comm π, mul_le_mul_iff_of_pos_right Real.pi_pos,
    (by norm_num : (0.63006 : ℝ) = (0.63006 : ℚ)), Rat.cast_le]
  native_decide
