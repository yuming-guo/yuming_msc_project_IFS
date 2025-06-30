-- import Mathlib.Analysis.InnerProductSpace.PiL2
-- import Mathlib.Order.CompletePartialOrder
import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Bornology EMetric ENNReal

namespace coursework2 -- sets up the namespace

/-
In coursework 2, I attempt to formalise the proof of theorem 9.1 in the textbook
'Fractal Geometry: Mathematical Foundations and Applications'. It can be described
as follows:

Consider the iterated function system given by the contractions {S_1, ..., S_m} on
D ⊂ ℝ^n, so that
|S_i(x) - S_i(y)| ≤ c_i|x - y|, (x, y) ∈ D
with c_i < 1 for each i. Then there is a unique attractor F, i.e. a non-empty
compact set such that
F = ⋃(i = 1 to m) S_i(F).
-/

/- This is the lemma that, in ENNReals, if b is non-infinity and a > 0, then b ≤ c means b < c + a.
To be added into mathlib. -/
-- Third proof, by Bhavik (24/02), first two proofs saved in alt_proofs.lean for version control
lemma lt_add_of_le_of_pos_ENNReal {a b c : ENNReal} (ha : a ≠ 0) (hb : b ≠ ⊤) (hbc : b ≤ c) :
    b < c + a := by
  obtain rfl | hbc := eq_or_lt_of_le hbc
  · exact lt_add_right hb ha
  exact lt_add_of_lt_of_nonneg hbc (zero_le _)

-- here we prove the LipschitzWith.weaken lemma, except for LipschitzOnWith
lemma LipschitzOnWithWeaken {α : Type} {β : Type} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {s : Set α} {K K' : NNReal} {f : α → β} (hf : LipschitzOnWith K f s) (hK : K ≤ K') :
      LipschitzOnWith K' f s := by
  delta LipschitzOnWith at *
  intro x hx y hy
  have h1 : K * edist x y ≤ K' * edist x y := by gcongr -- le_implies_mul_le hK
  exact Preorder.le_trans (edist (f x) (f y)) (↑K * edist x y) (↑K' * edist x y) (hf hx hy) h1

/- Define some variables: D ∈ ℝ^n, define c and f, indexed by ι - f i corresponds to the individual
S_is in the informal proof, c i corresponds to each indiviual c_is, the factors in the contraction.
Finally we define S to be the union of all S_is. -/
variable (n : ℕ) {D : Set (EuclideanSpace ℝ (Fin n))} {ι : Type*} [Fintype ι] (c : ι → NNReal)
  (i : ι) {f : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (ε : ENNReal)
  (x : EuclideanSpace ℝ (Fin n)) {S : Set (EuclideanSpace ℝ (Fin n)) → Set (EuclideanSpace ℝ (Fin n))}

-- this is the lemma that contractions map bounded sets to bounded sets
lemma contr_maps_bounded_to_bounded (hc : ∀ i, c i < 1)
    (hSi : ∀ i, LipschitzOnWith (c i) (f i) D) :
    ∀ A ⊆ D, IsBounded A → IsBounded (f i '' A) := by
  intro A hAD hA
  rw [Metric.isBounded_iff] at hA
  rw [Metric.isBounded_iff]
  rcases hA with ⟨C, hC⟩
  have h1 : ∀ x ∈ A, ∀ y ∈ A, dist (f i x) (f i y) ≤ C := by
    intro x hx y hy
    apply?
    sorry
  sorry

/- The lemma that d(S(A), S(B) ≤ max_{1 ≤ i ≤ m} d(S_i(A), S_i(B).
Let it such that if x is in D, then S_i(x) is in D; Define S(A) to be the union of all S_i(A)s. -/
theorem dist_union_le_max_dist_ind (hfi : ∀ i, Set.MapsTo (f i) D D) (hD : IsCompact D)
    (hS : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsCompact A → S A = ⋃ i, (f i '' A))
    (hc : ∀ i, c i < 1) (hSi : ∀ i, LipschitzOnWith (c i) (f i) D):
    ∀ A B, A.Nonempty → B.Nonempty → IsCompact A → IsCompact B → A ⊆ D → B ⊆ D →
      hausdorffEdist (S A) (S B) ≤ ⨆ i, hausdorffEdist (f i '' A) (f i '' B) := by
  -- first we prove that D is bounded
  have hD' : IsBounded D := IsCompact.isBounded hD

  intro A B hAn hBn hAc hBc hAD hBD
  -- This lemma bounds the hausdorff distance between two sets
  apply hausdorffEdist_le_of_mem_edist

  /- Now show that for any point in each set, there exists another point in the other set within
  the bound -/
  · intro x hx
    rw [hS] at hx

    · simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hx⟩ := hx

      have h1 : ∀ ε : ENNReal, ε ≠ 0 → hausdorffEdist (f i '' A) (f i '' B)
          < (⨆ i, hausdorffEdist (f i '' A) (f i '' B)) + ε := by
        intro ε hε

        have h1' : hausdorffEdist (f i '' A) (f i '' B)
            ≤ ⨆ i, hausdorffEdist (f i '' A) (f i '' B) := le_iSup_iff.mpr fun b a => a i

        have h1b : hausdorffEdist (f i '' A) (f i '' B) ≠ ⊤ := by
          -- two sets nonmpty and bounded implies finite hausdorff distance
          apply Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded

          -- here we need 4 things: (f i '' A) and (f i '' B) each nonempty, and bounded
          · exact Set.Nonempty.image (f i) hAn
          · exact Set.Nonempty.image (f i) hBn
          · have h1ba : IsBounded A := IsBounded.subset hD' hAD
            exact contr_maps_bounded_to_bounded n c i hc hSi A h1ba -- this is a lemma to be proven
          · have h1bb : IsBounded B := IsBounded.subset hD' hBD
            exact contr_maps_bounded_to_bounded n c i hc hSi B h1bb -- same as above
        exact lt_add_of_le_of_pos_ENNReal hε h1b h1' -- apply the lemma we proved earlier

      have h2 : ∀ ε, 0 < ε → ∃ y ∈ S B,
          edist x y < (⨆ i, hausdorffEdist (f i '' A) (f i '' B)) + ε := by
        intro ε hε

        have h2' : ∀ ε, ε ≠ 0 → ∃ y ∈ f i '' B,
            edist x y < (⨆ i, hausdorffEdist (f i '' A) (f i '' B)) + ε := by
          exact fun ε a => exists_edist_lt_of_hausdorffEdist_lt hx (h1 ε a)

        have hε' : ε ≠ 0 := Ne.symm (ne_of_lt hε)
        obtain ⟨y, hy, hxy⟩ := h2' ε hε'

        have h2b : y ∈ S B := by
          -- Probably need IsCompact B here
          have h2b' : (f i '' B) ⊆ S B := by
            rw [hS]
            · exact Set.subset_iUnion_of_subset i fun ⦃a⦄ a => a
            · exact hBc
          exact h2b' hy
        use y

      sorry -- exact le_of_forall_pos_lt_add h2?
    · exact hAc -- we need to prove A is compact here, similar to the IsCompact B requirement above
  · sorry  -- this one is the same as the 1st goal, just different order of A and B

-- This it the theorem that for each IFS, there exists a unique (non-empty compact) attractor F
theorem attractor_uniq (hfi : ∀ i, Set.MapsTo (f i) D D) (hc : ∀ i, c i < 1) (hε : ε > 0)
    (hD : IsCompact D) (hSi : ∀ i, LipschitzOnWith (c i) (f i) D)
    (hS : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsCompact A → S A = ⋃ i, (f i '' A)) :
    ∃! A ⊆ D, S A = A := by
  have h1 : ∀ A B, A.Nonempty → B.Nonempty → IsCompact A → IsCompact B → A ⊆ D → B ⊆ D → hausdorffEdist (S A) (S B)
      ≤ ⨆ i, hausdorffEdist (f i '' A) (f i '' B) := dist_union_le_max_dist_ind n c hfi hD hS hc hSi

  have h2 : ∀ A B, A.Nonempty → B.Nonempty → IsCompact A → IsCompact B → A ⊆ D → B ⊆ D →
      hausdorffEdist (S A) (S B) ≤ (⨆ i, c i) * hausdorffEdist A B := by
    intro A B hAn hBn hAc hBc hAD hBD

    have hSi' : ∀ i, LipschitzOnWith (⨆ i, c i) (f i) D := by
      intro i

      have hci : ∀ i, (c i ≤ ⨆ i, c i) := by
        intro i
        refine le_ciSup ?_ _
        delta BddAbove at *
        delta upperBounds at *
        use 1
        simp
        exact fun a => le_of_lt (hc a)
      exact LipschitzOnWithWeaken (hSi i) (hci i)

    have h2a : ∀ i, ∀ A B, A.Nonempty → B.Nonempty → IsCompact A → IsCompact B → A ⊆ D → B ⊆ D →
        hausdorffEdist (f i '' A) (f i '' B) ≤ (⨆ i, c i) * hausdorffEdist A B := by
      intro i A' B' hAn' hBn' hAc' hBc' hAD' hBD'
      sorry
    sorry
  sorry

end coursework2

-- at its current shape, the code does not pass the linter, but this is expected as the proof is incomplete
