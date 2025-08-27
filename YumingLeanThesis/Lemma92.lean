import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lemma 9.2 in Falconer "Fractal Geometry: Mathematical Foundations and Applications"

This file contains a formalisation of the proof of Lemma 9.2 in Falconer's book.

# Main Results
* `there_is_no_lemma`: Maybe there will be something once I've actually proven something

# References
* [1] Kenneth Falconer, "Fractal Geometry: Mathematical Foundations and Applications", Wiley, 2003.
-/


open Bornology ENNReal EMetric IsCompact Topology MeasureTheory InnerProductSpace

namespace lemma92 -- sets up the namespace


lemma special_left_cancelativity {a c : ENNReal} {b d: NNReal} (ha : a ≠ ⊤) (hc : c ≠ ⊤) (hab : a = b) (hcd : c < d) :
    a + c < b + d := by
  rw [<-hab]
  have ha' : a = a.toNNReal := Eq.symm (coe_toNNReal ha)
  have hc' : c = c.toNNReal := Eq.symm (coe_toNNReal hc)
  rw [ha', hc']
  norm_cast
  simp only [add_lt_add_iff_left, gt_iff_lt]
  exact toNNReal_lt_of_lt_coe hcd

/- if radius is non-zero and non-infinity, then the closure of a ball is its respective closed ball.
This lemma exists already for Metric, here we port it to EMetric. -/
lemma closure_of_ball_eq_closedBall {E : Type} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (x : E)
    {r : NNReal} (hr : r ≠ 0) : closure (ball x r) = closedBall x r := by
  -- firstly, finite radius means closed balls in EMetric and Metric are equivalent
  have h_closedball_equiv : closedBall x r = Metric.closedBall x r := Metric.emetric_closedBall_nnreal

  -- finite radius also means open balls in EMetric and Metric are equivalent
  have h_ball_equiv : ball x r = Metric.ball x r := Metric.emetric_ball_nnreal

  -- therefore the closures of open balls in EMetric and Metric are also equivalent
  have h_closure_ball_equiv : closure (ball x r) = closure (Metric.ball x r) := by rw [h_ball_equiv]

  -- finally, use the fact that closure of a Metric ball is the closed ball
  have hr' : r.toReal ≠ 0 := NNReal.coe_ne_zero.mpr hr
  have h_metric_closed_ball : closure (Metric.ball x r) =
      Metric.closedBall x r := closure_ball x hr'

  rw [h_closedball_equiv, h_closure_ball_equiv]
  exact h_metric_closed_ball


variable {n : ℕ} {ι : Type*} {x : EuclideanSpace ℝ (Fin n)}
  {V : ι → Set (EuclideanSpace ℝ (Fin n))}

-- EuclideanSpace.volume_ball

theorem lemma_92 {a₁ a₂ r : NNReal} (hDis : ∀ (i j : ι), i ≠ j → Disjoint (V i) (V j))
    (hV₁ : ∀ i, ∃ x₁ ∈ V i, ball x₁ (a₁ * r) ⊆ V i) (hn : 0 < n)
    (hV₂ : ∀ i, ∃ x₂ : EuclideanSpace ℝ (Fin n), ∀ y₂, y₂ ∈ V i → y₂ ∈ ball x₂ (a₂ * r))
    (hV₃ : ∀ i, IsOpen (V i)) (hr : r ≠ 0) (ha₂ : a₂ ≠ 0) :
    {i : ι | (ball x r ∩ closure (V i)).Nonempty}.encard.toENNReal ≤ ((1 + 2 * a₂) ^ n / a₁ ^ n) := by
  set Q : Set ι :=  {i : ι | (ball x r ∩ closure (V i)).Nonempty}
  set q : ENat := Q.encard

  -- set up the assumption for below
  have h_coeff : a₂ * r ≠ 0 := by
    have h_coeff' : a₂ * r ≠ 0 := (mul_ne_zero_iff_right hr).mpr ha₂
    norm_cast

  -- first line of the informal proof
  have h₁ : ∀ i, (closure (V i) ∩ (ball x r)).Nonempty → closure (V i) ⊆ ball x ((1 + 2 * a₂) * r) := by
    intro i hVi
    -- here: x is the centre of B (see informal proof), p is any point in the closure of V i, and
    -- y is a point in closure(V i) ∩ B (which is nonempty by assumption)
    have h₁a : ∀ p ∈ closure (V i), edist p x < (1 + 2 * a₂) * r := by
      intro p hp
      -- dissect the distance into two parts using an intermediate point y
      have hy₁ : ∀ y ∈ closure (V i) ∩ (ball x r), edist p y ≤ (2 * a₂) * r ∧ edist y x < r := by
        intro y hy
        constructor

        -- first part of the distance via closures and closed balls
        · specialize hV₂ i
          -- we obtain w, the centre of the external ball of V i
          cases' hV₂ with w hyw

          -- rewrite the assumption hyw to a more convenient form
          have hyw' : V i ⊆ ball w (a₂ * r) := hyw
          -- since V i is contained by the external ball, this is preserved by closure
          have h_closed : closure (V i) ⊆ closure (ball w (a₂ * r)) := closure_mono hyw'
          -- We pvove p is in the closed ball with center w and radius a₂r
          have h_closedball : closure (ball w (a₂ * r)) =
              closedBall w (a₂ * r) := closure_of_ball_eq_closedBall w h_coeff

          have hpw : edist p w ≤ a₂ * r := by
            -- we prove that in EMetricSpace, the closure of the ball is the closed ball
            rw [h_closedball] at h_closed
            exact h_closed hp

          -- now we know that y is in the closed ball with center w and radius a₂r
          have hwy : edist w y ≤ a₂ * r := by
            have y_closed_ball : y ∈ closedBall w (a₂ * r) := by
              obtain ⟨hyc, _⟩ := hy
              rw [h_closedball] at h_closed
              exact h_closed hyc
            delta closedBall at y_closed_ball
            rw [edist_comm]
            exact y_closed_ball

          -- now we sum then together and apply the triangle inequality
          have hpwy : edist p w + edist w y ≤ 2 * (a₂ * r) := by
            calc
              edist p w + edist w y ≤ a₂ * r + a₂ * r := add_le_add hpw hwy
              _ ≤ 2 * (a₂ * r) := by
                norm_cast
                rw [Eq.symm (two_mul (a₂ * r))]
          have : 2 * a₂ * r = 2 * (a₂ * r) := by
            rw [mul_assoc]
          have hpwy' : edist p w + edist w y ≤ (2 * a₂) * r := by
            rw [mul_assoc]
            exact hpwy
          have h_triangle : edist p y ≤ edist p w + edist w y := by simp only [edist_triangle]
          exact le_trans h_triangle hpwy'

          -- d(x,y) < r directly from the assumption
        · obtain ⟨_, hyb⟩ := hy
          exact hyb

      -- finally apply triangle inequality
      have hpxy : ∀ (y : EuclideanSpace ℝ (Fin n)), edist p x ≤ edist p y + edist y x := by
        intro y
        simp only [edist_triangle]

      -- we know the intersection between closure(V i) and B is nonempty, so we extract the point
      rw [Set.nonempty_def] at hVi
      obtain ⟨y, hyVb⟩ := hVi
      specialize hy₁ y hyVb
      specialize hpxy y
      obtain ⟨h_dpy, h_dyx⟩ := hy₁
      rw [le_iff_lt_or_eq] at h_dpy
      -- assemble the strict inequality and the less than or equal to together
      have h_sum: edist p y + edist y x < (1 + 2 * a₂) * r := by
        ring_nf
        rw [mul_comm, <- mul_assoc]
        -- here i found it easier to break down by equality between d(p,y) and upper bound 2a₂r
        cases' h_dpy with h_dpy₁ h_dpy₂
        · exact ENNReal.add_lt_add h_dpy₁ h_dyx
        · exact special_left_cancelativity (edist_ne_top p y) (edist_ne_top y x) h_dpy₂ h_dyx

      exact lt_of_le_of_lt hpxy h_sum
    exact h₁a

  /- for i and j such that V i and V j both intersect B, then: their respective interior balls are
  disjoint and are each contained in the ball cocentric with B with radius (1 + 2a₂) * r. -/
  have h₂ : ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → ∃ x₁ ∈ V i, ball x₁ (a₁ * r) ⊆ V i ∧
      ∃ x₂ ∈ V j, ball x₂ (a₁ * r) ⊆ V j ∧ ball x₁ (a₁ * r) ⊆ ball x ((1 + 2 * a₂) * r) ∧
      ball x₂ (a₁ * r) ⊆ ball x ((1 + 2 * a₂) * r) ∧
      Disjoint (ball x₁ (a₁ * r)) (ball x₂ (a₁ * r)) := by
    intro i hi j hj hij

    obtain ⟨x₁, hx₁a, hx₁b⟩ := hV₁ i
    refine Exists.intro x₁ ⟨hx₁a, hx₁b, ?_⟩
    obtain ⟨x₂, hx₂a, hx₂b⟩ := hV₁ j
    refine Exists.intro x₂ ⟨hx₂a, hx₂b, ?_, ?_, ?_⟩
    · have hVi : V i ⊆ closure (V i) := subset_closure
      specialize h₁ i
      have hx₁c : closure (V i) ⊆ ball x ((1 + 2 * a₂) * r) := by
        refine h₁ ?_
        simpa [Q, Set.inter_comm] using hi
      exact subset_trans (subset_trans hx₁b hVi) hx₁c
    · have hVj : V j ⊆ closure (V j) := subset_closure
      specialize h₁ j
      have hx₂c : closure (V j) ⊆ ball x ((1 + 2 * a₂) * r) := by
        refine h₁ ?_
        simpa [Q, Set.inter_comm] using hj
      exact subset_trans (subset_trans hx₂b hVj) hx₂c
    · exact Set.disjoint_of_subset hx₁b hx₂b (hDis i j hij)


  have h₃ : ∑' i : Q, volume (closure (V i) ∩ ball x r) ≤ volume (ball x ((1 + 2 * a₂) * r)) := by

    have h₃a : ⋃ i : Q, (closure (V i) ∩ ball x r) ⊆ ball x ((1 + 2 * a₂ * r)) := by
      sorry
    -- MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint
    sorry
  sorry

end lemma92
