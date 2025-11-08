import Ray.Dynamics.Multibrot.RayEqn
import Series.Analysis.ContDiff
import Series.Analysis.Small
import Series.Series.Shift
import Series.Series.Sqrt

/-!
# Power series computation of `pray` via `cascade`
-/

open Function (uncurry)
open scoped Topology
variable {d n k f : ℕ} {m : WithTop ℕ∞} [d2 : Fact (2 ≤ d)]
variable {z p : ℂ}

/-!
### Facts about `cascade`
-/

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

/-!
### Express `pray` in terms of `cascade` with high `n`, to get an equation for `pray`

TODO: We could use `k ≤ 2 ^ (n + 1) - 2` instead of `2 ^ n - 1` in `descent` with a bit more work,
which would save ~one iteration in the `descent` loop.
-/

-- From here on, we fix `d = 2`
variable [Fact (2 ≤ 2)]

/-- `descent z (pray 2 z) k n (k + 1) = pray 2 z`, expressing low-`n` cascade values via higher -/
noncomputable def descent (k n : ℕ) (z p : ℂ) (f : ℕ) : ℂ := match f with
  | 0 => cascade 2 n z
  | f + 1 =>
    if k < 2 ^ n then cascade 2 n z else
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
  · simp only [descent, ite_eq_left_iff]
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

/-!
### The derivative of `descent`
-/

/-- The derivative of `descent` w.r.t. `p` -/
noncomputable def descent_p (k n : ℕ) (z p : ℂ) (f : ℕ) : ℂ := match f with
  | 0 => 0
  | f + 1 =>
    if k < 2 ^ n then 0 else
    (descent_p k (n + 1) z p f - z ^ (2 ^ (n + 1) - 1)) / (2 * descent k n z p (f + 1))

/-- The derivative of `descent` w.r.t. `p` is given by `descent_p` -/
lemma hasDerivAt_descent : ∀ᶠ q in 𝓝 (0,1),
    HasDerivAt (fun p ↦ descent k n q.1 p f) (descent_p k n q.1 q.2 f) q.2 := by
  induction' f with f h generalizing n
  · simp only [descent, descent_p, hasDerivAt_const, Filter.eventually_true]
  · simp only [descent, descent_p, mul_ite]
    split_ifs with lt
    · simp only [hasDerivAt_const, Filter.eventually_true]
    · have nz : 2 ^ (n + 1) - 1 ≠ 0 := by simp [Nat.sub_eq_zero_iff_le]
      have m : descent k (n + 1) 0 1 f - 0 ^ (2 ^ (n + 1) - 1) * 1 ∈ Complex.slitPlane := by
        simp only [descent_zero, zero_pow nz, mul_one, sub_zero, Complex.one_mem_slitPlane]
      have c : ContinuousAt (fun q : ℂ × ℂ ↦
          descent k (n + 1) q.1 q.2 f - q.1 ^ (2 ^ (n + 1) - 1) * q.2) (0,1) :=
        contDiffAt_descent (m := ⊤).continuousAt.sub (by fun_prop)
      filter_upwards [h, c.eventually_mem (Complex.isOpen_slitPlane.eventually_mem m)]
        with ⟨z,p⟩ h m
      exact (h.sub (hasDerivAt_const_mul _)).csqrt m

/-- `descent` is degenerate, which means `p - descent ... p f` will be nondegenerate -/
lemma deriv_descent : deriv (fun p ↦ descent k n 0 p f) 1 = 0 := by
  induction' f with f h generalizing n
  · simp only [descent_zero, deriv_const']
  · simp only [descent, cascade_z0, descent_zero]
    split_ifs with lt
    · simp only [deriv_const']
    · have nz : 2 ^ (n + 1) - 1 ≠ 0 := by simp [Nat.sub_eq_zero_iff_le]
      simp only [zero_pow nz, zero_mul, sub_zero, Complex.sqrt_one, deriv_const']

/-!
### Series computation of `descent` and `descent_p`
-/

variable {α : Type} [SeriesScalar α] [ApproxSeries α ℂ] [Div2 α] [ApproxDiv2 α ℂ]

/-- `Series` computation of `descent` and `descent_p` -/
def Series.descent (k n : ℕ) (p : Series α) (f : ℕ) : Series α × Series α := match f with
  | 0 => (.withOrder 1 k, .withOrder 0 k)
  | f + 1 =>
    if k < 2 ^ n then (.withOrder 1 k, .withOrder 0 k) else
    let s := 2 ^ (n + 1) - 1
    let (a, da) := p.descent k (n + 1) f
    let b := sqrt (a - p <<< s)
    let db := div2 ((da - (1 : Series α) <<< s) * b.inv 1)
    (b, db)

omit [Div2 α] in
@[approx] lemma approx_one_cascade (le : k ≤ 2 ^ n) :
    approx (.withOrder 1 k : Series α) (cascade 2 n) := by
  intro i lt
  simp only [Series.order_withOrder, Nat.cast_lt] at lt
  refine ⟨(cascade_analytic (by simp)).of_le le_top, ?_⟩
  simp only [Series.extend_withOrder, Nat.cast_lt, lt, ↓reduceIte, Series.extend_one, series_coeff,
    iteratedDeriv_cascade (trans lt le), smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h <;> simp [h]

@[approx] lemma approx_descent {p : Series α} {p' : ℂ → ℂ} (ap : approx p p') (fuel : k - n ≤ f) :
    approx (p.descent k n f).1 (fun z ↦ descent k n z (p' z) f) := by
  induction' f with f h generalizing n
  · simp only [descent, Series.descent]
    simp only [nonpos_iff_eq_zero, Nat.sub_eq_zero_iff_le] at fuel
    exact approx_one_cascade (le_trans fuel Nat.lt_two_pow_self.le)
  · simp only [Series.descent, descent]
    split_ifs with kn
    · exact approx_one_cascade (by omega)
    · refine Series.approx_sqrt ?_ (by simp [Nat.sub_eq_zero_iff_le])
      exact approx_sub (h (by omega)) (by approx)

@[approx] lemma approx_descent_p {p : Series α} {p' : ℂ → ℂ} (ap : approx p p') (fuel : k - n ≤ f) :
    approx (p.descent k n f).2 (fun z ↦ descent_p k n z (p' z) f) := by
  induction' f with f h generalizing n
  · exact Series.approx_withOrder approx_zero (by simp)
  · simp only [Series.descent, descent_p]
    split_ifs with kn
    · exact Series.approx_withOrder approx_zero (by simp)
    · simp only [div_eq_mul_inv, mul_inv, ← mul_assoc _ _⁻¹, mul_comm _ (2 : ℂ)⁻¹, mul_assoc _⁻¹]
      simp only [← div2_eq_mul]
      refine approx_div2 (approx_mul (approx_sub (h (by omega)) (by approx)) ?_)
      refine Series.approx_inv ?_ (by simp) (by simp)
      simpa only [descent, kn, ↓reduceIte, Series.descent] using approx_descent ap fuel
