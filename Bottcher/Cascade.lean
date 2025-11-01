import Ray.Dynamics.Multibrot.RayEqn
import Series.Analysis.ContDiff
import Series.Analysis.Small

/-!
# Power series computation of `pray` via `cascade`
-/

variable {d n k : ℕ} [Fact (2 ≤ d)]

/-- Low-order derivatives of `cascade` -/
lemma iteratedDeriv_cascade (lt : k < d ^ n) :
    iteratedDeriv k (cascade d n) 0 = if k = 0 then 1 else 0 := by
  have ca := cascade_analytic (d := d) (n := n) (z := 0) (by simp)
  suffices h : iteratedDeriv k (cascade d n - 1) 0 = 0 by
    rwa [iteratedDeriv_sub, Pi.one_def, iteratedDeriv_const, sub_eq_zero] at h
    · exact ca.of_le le_top
    · exact contDiffAt_const
  refine iteratedDeriv_eq_zero_of_small ?_ ?_ lt
  · exact ((ca.sub contDiffAt_const).of_le le_top)
  · simpa using (cascade_approx (d := d) (n := n)).norm_right
