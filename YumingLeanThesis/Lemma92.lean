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


open Bornology ENNReal EMetric IsCompact Topology MeasureTheory

namespace lemma92 -- sets up the namespace

lemma why_do_i_have_to_prove_this {a b c : ENNReal} (hac : a ≤ c) (hbc : b < c) : a + b ≤ 2 * c := by
  have hbc' : b ≤ c := le_of_lt hbc
  have h₁ : a + b ≤ c + c := add_le_add hac hbc'
  have h₂ : c + c = 2 * c := Eq.symm (two_mul c)
  rw [h₂] at h₁
  exact h₁

lemma why_do_i_have_to_prove_this' {a b : ENNReal} : 2 * a * b = 2 * (a * b) := mul_assoc 2 a b

variable {n : ℕ} {ι : Type*} (x : EuclideanSpace ℝ (Fin n))
  {V : ι → Set (EuclideanSpace ℝ (Fin n))}

-- EuclideanSpace.volume_ball

theorem lemma_92 {a₁ a₂ r : NNReal} (hDis : ∀ (i j : ι), i ≠ j → Disjoint (V i) (V j))
    (hV₁ : ∀ i, ∃ x₁ ∈ V i, ball x₁ (a₁ * r) ⊆ V i)
    (hV₂ : ∀ i, ∃ x₂ : EuclideanSpace ℝ (Fin n), ∀ y₂, y₂ ∈ V i → y₂ ∈ ball x₂ (a₂ * r))
    (hV₃ : ∀ i, IsOpen (V i)) (hr : r ≠ 0) (ha₂ : a₂ ≠ 0) :
    {i : ι | (ball x r ∩ closure (V i)).Nonempty}.encard.toENNReal ≤ ((1 + 2 * a₂) ^ n / a₁ ^ n) := by
  set Q : Set ι :=  {i : ι | (ball x r ∩ closure (V i)).Nonempty}
  set q : ENat := Q.encard

  -- set up the assumption for below
  have h_coeff : a₂.toReal * r.toReal ≠ 0 := by
    have h_coeff' : a₂ * r ≠ 0 := (mul_ne_zero_iff_right hr).mpr ha₂
    norm_cast

  -- first line of the informal proof
  have h₁ : ∀ i, closure (V i) ∩ (ball x r) ≠ ∅ → closure (V i) ⊆ ball x ((1 + 2 * a₂) * r) := by
    intro i hVi
    have h₁a : ∀ p ∈ closure (V i), edist p x < (1 + 2 * a₂) * r := by
      intro p hp
      -- dissect the distance into two parts using an intermediate point y
      have hy₁ : ∀ y ∈ V i ∩ (ball x r), edist p y ≤ (2 * a₂) * r ∧ edist y x < r := by
        intro y hy
        constructor

        -- first part of the distance via closures and closed balls
        · specialize hV₂ i
          -- we obtain w, the centre of the external ball of V i
          cases' hV₂ with w hyw

          -- We pvove p is in the closed ball with center w and radius a₂r
          have hpw : edist p w ≤ a₂ * r := by
            have hyw' : V i ⊆ ball w (a₂ * r) := hyw
            -- since V i is contained by the external ball, this is preserved by closure
            have h_closed : closure (V i) ⊆ closure (ball w (a₂ * r)) := closure_mono hyw'

            -- we prove that in EMetricSpace, the closure of the ball is the closed ball
            have h_closedball : closure (ball w (a₂ * r)) = closedBall w (a₂ * r) := by

              -- firstly, finite radius means closed balls in EMetric and Metric are equivalent
              have h_closeball_equiv : closedBall w (a₂ * r) = Metric.closedBall w (a₂ * r) := by
                exact Metric.emetric_closedBall_nnreal

              -- finite radius also means open balls in EMetric and Metric are equivalent
              have h_ball_equiv : ball w (a₂ * r) = Metric.ball w (a₂ * r) := Metric.emetric_ball_nnreal
              -- therefore the closures of open balls in EMetric and Metric are also equivalent
              have h_closure_ball_equiv : closure (ball w (a₂ * r)) =
                  closure (Metric.ball w (a₂ * r)) := by rw [h_ball_equiv]

              -- finally, use the fact that closure of a Metric ball is the closed ball
              have h_metric_closed_ball : closure (Metric.ball w (a₂ * r)) =
                  Metric.closedBall w (a₂ * r) := by
                exact closure_ball w h_coeff

              rw [h_closeball_equiv, h_closure_ball_equiv]
              exact h_metric_closed_ball
            rw [h_closedball] at h_closed
            exact h_closed hp

          -- now we know that y is in the open ball with center w and radius a₂r
          have hwy : edist w y < a₂ * r := by
            obtain ⟨hyVi, _⟩ := hy
            specialize hyw y hyVi
            simp [ball] at hyw
            rw [edist_comm] at hyw
            exact hyw

          -- now we sum then together and apply the triangle inequality
          have hpwy : edist p w + edist w y ≤ 2 * (a₂ * r) := by
            exact why_do_i_have_to_prove_this hpw hwy
          have : 2 * a₂ * r = 2 * (a₂ * r) := by
            rw [mul_assoc]
          have hpwy' : edist p w + edist w y ≤ (2 * a₂) * r := by
            rw [<- why_do_i_have_to_prove_this'] at hpwy
            exact hpwy
          have h_triangle : edist p y ≤ edist p w + edist w y := by simp only [edist_triangle]
          exact le_trans h_triangle hpwy'

          -- d(x,y) < r directly from the assumption
        · obtain ⟨_, hyb⟩ := hy
          exact hyb

      have hpxy : ∀ (y : EuclideanSpace ℝ (Fin n)), edist p x ≤ edist p y + edist y x := by
        intro y
        simp only [edist_triangle]


      sorry

    exact h₁a

  have h₂ : ∀ i ∈ Q, volume (closure (V i) ∩ (ball x r)) ≤ (a₁ * r) ^ n := by
    intro i hi
    sorry
  have h₃ : ∑' i : Q, volume (closure (V i)) ≤ volume (ball x ((1 + 2 * a₂) * r)) := by
    -- MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint
    sorry
  sorry

end lemma92
