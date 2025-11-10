import Bottcher.Dyadic
import Bottcher.Pray
import Bottcher.Rat

/-!
# Actual computation of the Böttcher series for the Mandelbrot set
-/

/-- The first 10 terms -/
lemma spray_10 : (spray 10 : Series ℚ).c =
    #[1, -1/2, 1/8, -1/4, 15/128, 0, -47/1024, -1/16, 987/32768, 0] := by native_decide

-- More terms. Uncomment for fun!
-- #eval (spray 100 : Series Dyadic).c
