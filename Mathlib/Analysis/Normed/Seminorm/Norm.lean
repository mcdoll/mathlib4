module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Seminorm.Basic


@[expose] public section

assert_not_exists balancedCore

open Set

variable {𝕜 E F : Type*}

/-! # The norm as a seminorm -/


section normSeminorm

variable (𝕜) (E) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℝ}

/-- The norm of a seminormed group as a seminorm. -/
def normSeminorm : Seminorm 𝕜 E :=
  { normAddGroupSeminorm E with smul' := norm_smul }

@[simp]
theorem coe_normSeminorm : ⇑(normSeminorm 𝕜 E) = norm :=
  rfl

@[simp]
theorem ball_normSeminorm : (normSeminorm 𝕜 E).ball = Metric.ball := by
  ext x r y
  simp only [Seminorm.mem_ball, Metric.mem_ball, coe_normSeminorm, dist_eq_norm]

@[simp]
theorem closedBall_normSeminorm : (normSeminorm 𝕜 E).closedBall = Metric.closedBall := by
  ext x r y
  simp only [Seminorm.mem_closedBall, Metric.mem_closedBall, coe_normSeminorm, dist_eq_norm]

variable {𝕜 E} {x : E}

/-- Balls at the origin are absorbent. -/
theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Metric.ball (0 : E) r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).absorbent_ball_zero hr

/-- Balls containing the origin are absorbent. -/
theorem absorbent_ball (hx : ‖x‖ < r) : Absorbent 𝕜 (Metric.ball x r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).absorbent_ball hx

/-- Balls at the origin are balanced. -/
theorem balanced_ball_zero : Balanced 𝕜 (Metric.ball (0 : E) r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_ball_zero r

/-- Closed balls at the origin are balanced. -/
theorem balanced_closedBall_zero : Balanced 𝕜 (Metric.closedBall (0 : E) r) := by
  rw [← closedBall_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_closedBall_zero r

/-- If there is a scalar `c` with `‖c‖>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `‖c‖`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
lemma rescale_to_shell_semi_normed_zpow {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε) {x : E}
    (hx : ‖x‖ ≠ 0) :
    ∃ n : ℤ, c ^ n ≠ 0 ∧ ‖c ^ n • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖c ^ n • x‖) ∧
      (‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  (normSeminorm 𝕜 E).rescale_to_shell_zpow hc εpos hx

/-- If there is a scalar `c` with `‖c‖>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `‖c‖`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
lemma rescale_to_shell_semi_normed {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε)
    {x : E} (hx : ‖x‖ ≠ 0) :
    ∃ d : 𝕜, d ≠ 0 ∧ ‖d • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖d • x‖) ∧ (‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  (normSeminorm 𝕜 E).rescale_to_shell hc εpos hx

lemma rescale_to_shell_zpow [NormedAddCommGroup F] [NormedSpace 𝕜 F] {c : 𝕜} (hc : 1 < ‖c‖)
    {ε : ℝ} (εpos : 0 < ε) {x : F} (hx : x ≠ 0) :
    ∃ n : ℤ, c ^ n ≠ 0 ∧ ‖c ^ n • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖c ^ n • x‖) ∧
      (‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  rescale_to_shell_semi_normed_zpow hc εpos (norm_ne_zero_iff.mpr hx)

/-- If there is a scalar `c` with `‖c‖>1`, then any element can be moved by scalar multiplication to
any shell of width `‖c‖`. Also recap information on the norm of the rescaling element that shows
up in applications. -/
lemma rescale_to_shell [NormedAddCommGroup F] [NormedSpace 𝕜 F] {c : 𝕜} (hc : 1 < ‖c‖)
    {ε : ℝ} (εpos : 0 < ε) {x : F} (hx : x ≠ 0) :
    ∃ d : 𝕜, d ≠ 0 ∧ ‖d • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖d • x‖) ∧ (‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  rescale_to_shell_semi_normed hc εpos (norm_ne_zero_iff.mpr hx)

end normSeminorm
