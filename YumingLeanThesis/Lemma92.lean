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

variable {n : ℕ} {ι : Type*} (x : EuclideanSpace ℝ (Fin n))
  {V : ι → Set (EuclideanSpace ℝ (Fin n))}

-- EuclideanSpace.volume_ball

theorem lemma_92 {a₁ a₂ r : NNReal} (hDis : ∀ (i j : ι), i ≠ j → Disjoint (V i) (V j))
    (hV₁ : ∀ i, ∃ x₁ ∈ V i, ball x₁ (a₁ * r) ⊆ V i)
    (hV₂ : ∀ i, ∃ x₂ : EuclideanSpace ℝ (Fin n), ∀ y₂, y₂ ∈ V i → y₂ ∈ ball x₂ (a₂ * r)) :
    {i : ι | (ball x r ∩ closure (V i)).Nonempty}.encard.toENNReal ≤ ((1 + 2 * a₂) ^ n / a₁ ^ n) := by
  set Q : Set ι :=  {i : ι | (ball x r ∩ closure (V i)).Nonempty}
  set q : ENat := Q.encard
  have h₁ : ∀ i, closure (V i) ∩ (ball x r) ≠ ∅ → closure (V i) ⊆ ball x ((1 + 2 * a₂) * r) := by
    intro i hVi
    have h₁a : ∀ p ∈ closure (V i), edist p x < (1 + 2 * a₂) * r := by
      intro p hp
      have hy₁ : ∀ y ∈ closure (V i) ∩ (ball x r), edist p y ≤ (2 * a₂) * r ∧ edist y x < r := by
        intro y hy
        constructor
        · sorry
        · obtain ⟨_, hyb⟩ := hy
          exact hyb


      have hpxy : ∀ (y : EuclideanSpace ℝ (Fin n)), edist p x ≤ edist p y + edist y x := by
        intro y
        simp only [edist_triangle]

      sorry

    exact h₁a

  have h₂ : ∀ i, closure (V i) ∩ (ball x r) ≠ ∅ → volume (closure (V i) ∩ (ball x r)) ≤ (a₁ * r) ^ n := by
    sorry
  have h₃ : ∑' i : Q, volume (closure (V i)) ≤ volume (ball x ((1 + 2 * a₂) * r)) := by
    -- MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint
    sorry
  sorry

end lemma92
