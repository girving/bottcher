import Ray.Dynamics.Multibrot.RayEqn
import Series.Analysis.ContDiff
import Series.Analysis.Small
import Series.Misc.Sqrt

/-!
# Power series computation of `pray` via `cascade`
-/

open Function (uncurry)
open scoped Topology
variable {d n k f : ℕ} {m : WithTop ℕ∞} [d2 : Fact (2 ≤ d)]
variable {z p : ℂ}

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

/-- `cascade` is flat for `n ≠ 0` -/
lemma deriv_cascade (n0 : n ≠ 0) : deriv (cascade d n) 0 = 0 := by
  have lt : 1 < d ^ n := Nat.one_lt_pow n0 (by have := d2.elim; omega)
  simpa using iteratedDeriv_cascade lt

-- From here on, we fix `d = 2`
variable [Fact (2 ≤ 2)]

/-- `descent z (pray 2 z) k n (k + 1) = pray 2 z`, expressing low-`n` cascade values via higher -/
noncomputable def descent (k n : ℕ) (z p : ℂ) (f : ℕ) : ℂ := match f with
  | 0 => cascade 2 n z
  | f + 1 =>
    if k ≤ 2 ^ (n + 1) - 1 then cascade 2 n z else
    Complex.sqrt (descent k (n + 1) z p f - z ^ (2 ^ (n + 1) - 1) * p)

/-- `descent` is monic -/
@[simp] lemma descent_zero : descent k n 0 p f = 1 := by
  induction' f with f h generalizing n
  · simp only [descent, cascade_z0]
  · simp only [descent]
    split_ifs with lt
    · simp only [cascade_z0]
    · rw [zero_pow]
      · simp [h]
      · simp [Nat.sub_eq_zero_iff_le]

/-- The key fact about `descent`, flexible fuel version -/
lemma descent_eq_cascade (fuel : k - n ≤ f) :
    ∀ᶠ z in 𝓝 0, descent k n z (pray 2 z) f = cascade 2 n z := by
  induction' f with f h generalizing n
  · simp only [descent, Filter.eventually_true]
  · simp only [descent, ite_eq_left_iff, not_le]
    have bo : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
    have r : ∀ᶠ z in 𝓝 0, 0 < (cascade 2 n z).re := by
      apply continuousAt_const.eventually_lt
      · exact Complex.continuous_re.continuousAt.comp (cascade_analytic (by simp)).continuousAt
      · simp only [cascade_z0, Complex.one_re, zero_lt_one]
    filter_upwards [h (n := n + 1) (by omega), bo.eventually_mem (by simp), r] with z h m r lt
    rw [h, cascade_succ m, add_sub_cancel_right, Complex.sqrt_sq r]

/-- The key fact about `descent`, specialized version -/
lemma descent_eq_pray : ∀ᶠ z in 𝓝 0, descent k 0 z (pray 2 z) k = pray 2 z := by
  have bo : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  filter_upwards [descent_eq_cascade (k := k) (n := 0) (f := k) (by omega),
    bo.eventually_mem (by simp)] with z e m
  simp only [e, cascade_zero m]

/-- `descent` is analytic -/
lemma contDiffAt_descent : ContDiffAt ℂ m (fun x : ℂ × ℂ ↦ descent k n x.1 x.2 f) (0, 1) := by
  induction' f with f h generalizing n
  · simp only [descent]
    exact ((cascade_analytic (by simp)).of_le le_top).comp _ contDiffAt_fst
  · simp only [descent]
    split_ifs with lt
    · exact ((cascade_analytic (by simp)).of_le le_top).comp _ contDiffAt_fst
    · refine (ContDiffAt.csqrt ?_).comp _ (h.sub (by fun_prop))
      simp only [descent_zero]
      rw [zero_pow]
      · simp
      · simp [Nat.sub_eq_zero_iff_le]
