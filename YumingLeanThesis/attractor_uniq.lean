-- import Mathlib.Analysis.InnerProductSpace.PiL2
-- import Mathlib.Order.CompletePartialOrder
import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniqueness of the Attractor of an IFS

This file contains a formalisation of the proof of the uniqueness of the attractor of an iterated
function system (IFS) in a metric space, as described in [1] p.124, Theorem 9.1, as well as some
auxiliary lemmas.

# Main Results
* `lt_add_of_le_of_pos_ENNReal`: The ENNReal version of the lemma `lt_add_of_le_of_pos`. If `b` is
  non-infinity and `a > 0`, then `b ≤ c` implies `b < c + a`.
* `LipschitzOnWith_Weaken`: The LipschitzOnWith version of the lemma `LipschitzWith.weaken`. If `f`
  is LipschitzOnWith with constant `K` on a set `s`, and `K ≤ K'`, then `f` is LipschitzOnWith with
  constant `K'` on the same set `s`.
* `contr_maps_bounded_to_bounded`: If `f` is a contraction mapping, then it maps bounded sets to
  bounded sets.
* `dist_union_le_max_dist_ind`: Let `S` be the union of the images of sets `A` and `B` under a
  family of contraction mappings `f i`, then the Hausdorff distance between `S(A)` and `S(B)` is
  bounded by the maximum Hausdorff distance between the images of `A` and `B` under each `f i`.
* `union_of_lipschitz_contracts`: If `S` is the union of the images of sets `A` and `B` under a
  family of contraction mappings `f i`, then the Hausdorff distance between `S(A)` and `S(B)` is
  bounded by the supremum of the individual lipschitz constants multiplied by the Hausdorff distance
  between `A` and `B`.

# References
* [1] Kenneth Falconer, "Fractal Geometry: Mathematical Foundations and Applications", Wiley, 2003.
-/


open Bornology Metric ENNReal EMetric

namespace attractor_uniq -- sets up the namespace


/- This is the lemma that, in ENNReals, if b is non-infinity and a > 0, then b ≤ c implies b < c + a.
To be added into mathlib. -/
lemma lt_add_of_le_of_pos_ENNReal {a b c : ENNReal} (ha : a ≠ 0) (hb : b ≠ ⊤) (hbc : b ≤ c) :
    b < c + a := by
  obtain rfl | hbc := eq_or_lt_of_le hbc
  · exact lt_add_right hb ha
  exact lt_add_of_lt_of_nonneg hbc (zero_le _)


-- here we prove the LipschitzWith.weaken lemma, except for LipschitzOnWith
lemma LipschitzOnWith_Weaken {α : Type} {β : Type} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {s : Set α} {K K' : NNReal} {f : α → β} (hf : LipschitzOnWith K f s) (hK : K ≤ K') :
      LipschitzOnWith K' f s := by
  delta LipschitzOnWith at *
  intro x hx y hy
  have h1 : K * edist x y ≤ K' * edist x y := by gcongr -- le_implies_mul_le hK
  exact Preorder.le_trans (edist (f x) (f y)) (↑K * edist x y) (↑K' * edist x y) (hf hx hy) h1


lemma exists_edist_le_of_hausdorffEdist_le {α : Type} {β : Type} [PseudoEMetricSpace α]
    {x : α} {s t : Set α} {r : ℝ≥0∞} (h : x ∈ s) (ht : t.Nonempty) (H : hausdorffEdist s t ≤ r) :
    ∃ y ∈ t, edist x y ≤ r := by
  by_cases hr : r = ⊤
  · rw [hr]
    simp only [le_top, and_true]
    exact ht
  · have H' : ∀ ε : ENNReal, 0 < ε → hausdorffEdist s t < r + ε := by
      intro ε hε
      refine lt_add_of_le_of_pos_ENNReal ?_ ?_ ?_
      · exact Ne.symm (ne_of_lt hε)
      · exact ne_top_of_le_ne_top hr H
      . exact H

    have h₁ : ∀ ε : ENNReal, 0 < ε → ∃ y ∈ t, edist x y < r + ε := by
      intro ε hε
      specialize H' ε hε
      exact exists_edist_lt_of_hausdorffEdist_lt h H'


    sorry


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
  -- unwrap boundedness definition
  rw [Metric.isBounded_iff] at hA
  rw [Metric.isBounded_iff]
  rcases hA with ⟨C, hC⟩

  -- we  show that the image of A under f i is bounded by C
  have h1 : ∀ x ∈ A, ∀ y ∈ A, dist (f i x) (f i y) ≤ C := by
    intro x hx y hy
    -- use the definition of Lipschitz condition of f i
    have h1a : ∀ x ∈ A, ∀ y ∈ A, dist (f i x) (f i y) ≤ c i * dist x y := by
      apply LipschitzOnWith.dist_le_mul
      exact LipschitzOnWith.mono (hSi i) hAD
    -- use the fact that the Lipschitz constant c i is less than 1 for all i
    have h1b : ∀ x ∈ A, ∀ y ∈ A, dist (f i x) (f i y) ≤ dist x y := by
      intro x hx y hy
      have h1b' : c i * dist x y ≤ dist x y := by -- does this really need to be a separate step?
        have h1b'' : c i ≤ 1 := le_of_lt (hc i)
        exact mul_le_of_le_one_left dist_nonneg h1b''
      specialize h1a x hx y hy
      exact le_trans' h1b' h1a
    have h1c : dist x y ≤ C := by simp_all only
    specialize h1b x hx y hy
    exact le_trans' h1c h1b

  -- this was all an aesop, perhaps can be simplified
  simp_all only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  apply Exists.intro
  · intro a a_1 a_2 a_3
    apply h1
    · exact a_1
    · exact a_3


/- The lemma that d(S(A), S(B) ≤ max_{1 ≤ i ≤ m} d(S_i(A), S_i(B).
Let it such that if x is in D, then S_i(x) is in D; Define S(A) to be the union of all S_i(A)s. -/
lemma dist_union_le_sup_ind_dist (hD : IsCompact D)
    (hS : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsCompact A → S A = ⋃ i, (f i '' A))
    (hc : ∀ i, c i < 1) (hSi : ∀ i, LipschitzOnWith (c i) (f i) D):
    ∀ A B, A.Nonempty → B.Nonempty → IsCompact A → IsCompact B → A ⊆ D → B ⊆ D →
      hausdorffEdist (S A) (S B) ≤ ⨆ i, hausdorffEdist (f i '' A) (f i '' B) := by
  -- first we prove that D is bounded
  have hD' : IsBounded D := IsCompact.isBounded hD
  intro A B hAn hBn hAc hBc hAD hBD

  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε h

  -- This lemma bounds the hausdorff distance between two sets
  apply hausdorffEdist_le_of_mem_edist

  /- Now show that for any point in each set, there exists another point in the other set within
  the bound -/
  · intro x hx
    rw [hS] at hx

    · simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hx⟩ := hx
      have h₁ : ∀ ε : ENNReal, ε ≠ 0 → hausdorffEdist (f i '' A) (f i '' B)
          < (⨆ i, hausdorffEdist (f i '' A) (f i '' B)) + ε := by
        intro ε hε
        have h₁' : hausdorffEdist (f i '' A) (f i '' B)
            ≤ ⨆ i, hausdorffEdist (f i '' A) (f i '' B) := le_iSup_iff.mpr fun b a => a i
        have h₁b : hausdorffEdist (f i '' A) (f i '' B) ≠ ⊤ := by
          -- two sets nonmpty and bounded implies finite hausdorff distance
          apply Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded
          -- here we need 4 things: (f i '' A) and (f i '' B) each nonempty, and bounded
          · exact Set.Nonempty.image (f i) hAn
          · exact Set.Nonempty.image (f i) hBn
          · have h₁b₁ : IsBounded A := IsBounded.subset hD' hAD
            exact contr_maps_bounded_to_bounded n c i hc hSi A hAD h₁b₁ -- this is a lemma to be proven
          · have h₁b₂ : IsBounded B := IsBounded.subset hD' hBD
            exact contr_maps_bounded_to_bounded n c i hc hSi B hBD h₁b₂ -- same as above
        exact lt_add_of_le_of_pos_ENNReal hε h₁b h₁' -- apply the lemma we proved earlier

      have h₂ : ∀ ε, 0 < ε → ∃ y ∈ S B,
          edist x y < (⨆ i, hausdorffEdist (f i '' A) (f i '' B)) + ε := by
        intro ε hε
        have h₂' : ∀ ε, ε ≠ 0 → ∃ y ∈ f i '' B,
            edist x y < (⨆ i, hausdorffEdist (f i '' A) (f i '' B)) + ε := by
          exact fun ε a => exists_edist_lt_of_hausdorffEdist_lt hx (h₁ ε a)
        have hε' : ε ≠ 0 := Ne.symm (ne_of_lt hε)
        obtain ⟨y, hy, hxy⟩ := h₂' ε hε'
        have h₂b : y ∈ S B := by
          have h₂b' : (f i '' B) ⊆ S B := by
            rw [hS]
            · exact Set.subset_iUnion_of_subset i fun ⦃a⦄ a => a
            · exact hBc
          exact h₂b' hy
        use y

      obtain ⟨y, hy, hy'⟩ := h₂ ε (by simpa)
      exact ⟨y, hy, hy'.le⟩
    · exact hAc -- we have from the definition that A is compact

    -- now we do the same for the other set - here commences the copy-paste
  · intro x hx
    rw [hS] at hx

    · simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hx⟩ := hx
      have h₁ : ∀ ε : ENNReal, ε ≠ 0 → hausdorffEdist (f i '' B) (f i '' A)
          < (⨆ i, hausdorffEdist (f i '' B) (f i '' A)) + ε := by
        intro ε hε
        have h₁' : hausdorffEdist (f i '' B) (f i '' A)
            ≤ ⨆ i, hausdorffEdist (f i '' B) (f i '' A) := le_iSup_iff.mpr fun b a => a i
        have h1b : hausdorffEdist (f i '' B) (f i '' A) ≠ ⊤ := by
          apply Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded
          · exact Set.Nonempty.image (f i) hBn
          · exact Set.Nonempty.image (f i) hAn
          · have h₁b₁ : IsBounded B := IsBounded.subset hD' hBD
            exact contr_maps_bounded_to_bounded n c i hc hSi B hBD h₁b₁
          · have h₁b₂ : IsBounded A := IsBounded.subset hD' hAD
            exact contr_maps_bounded_to_bounded n c i hc hSi A hAD h₁b₂
        exact lt_add_of_le_of_pos_ENNReal hε h1b h₁'

      have h₂ : ∀ ε, 0 < ε → ∃ y ∈ S A,
          edist x y < (⨆ i, hausdorffEdist (f i '' B) (f i '' A)) + ε := by
        intro ε hε
        have h₂' : ∀ ε, ε ≠ 0 → ∃ y ∈ f i '' A,
            edist x y < (⨆ i, hausdorffEdist (f i '' B) (f i '' A)) + ε := by
          exact fun ε a => exists_edist_lt_of_hausdorffEdist_lt hx (h₁ ε a)
        have hε' : ε ≠ 0 := Ne.symm (ne_of_lt hε)
        obtain ⟨y, hy, hxy⟩ := h₂' ε hε'
        have h₂b : y ∈ S A := by
          have h₂b' : (f i '' A) ⊆ S A := by
            rw [hS]
            · exact Set.subset_iUnion_of_subset i fun ⦃a⦄ a => a
            · exact hAc
          exact h₂b' hy
        use y

        -- after the copy-paste, all the hausdorffEdists are in the opposite order, so we reverse it
      have h₃ : ⨆ i, hausdorffEdist (f i '' B) (f i '' A) =
          ⨆ i, hausdorffEdist (f i '' A) (f i '' B) := by
        have h₃' : ∀ i, hausdorffEdist (f i '' B) (f i '' A) =
            hausdorffEdist (f i '' A) (f i '' B) := by
          intro i
          exact hausdorffEdist_comm
        exact iSup_congr h₃'
      rw [h₃] at h₂

        -- now that h2 is in the correct form, we return to copy-pasting
      obtain ⟨y, hy, hy'⟩ := h₂ ε (by simpa)
      exact ⟨y, hy, hy'.le⟩
    · exact hBc


-- now we move on to proving [1][p.125, equation 9.5], i.e. the union of the contractions has
-- lipschitz constant at most the supremum of the individual lipschitz constants
lemma union_of_lipschitz_contracts (hD : IsCompact D)
    (hS : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsCompact A → S A = ⋃ i, (f i '' A))
    (hc : ∀ i, c i < 1) (hSi : ∀ i, LipschitzOnWith (c i) (f i) D):
    ∀ A B, A.Nonempty → B.Nonempty → IsCompact A → IsCompact B → A ⊆ D → B ⊆ D →
      hausdorffEdist (S A) (S B) ≤ (⨆ i, c i) * hausdorffEdist A B := by
  intro A B hAn hBn hAc hBc hAD hBD

  -- we begin by applying the previous lemma
  have h : hausdorffEdist (S A) (S B) ≤
      (⨆ i, hausdorffEdist (f i '' A) (f i '' B)) := by
    exact dist_union_le_sup_ind_dist n c hD hS hc hSi A B hAn hBn hAc hBc hAD hBD

  have h' : ⨆ i, hausdorffEdist (f i '' A) (f i '' B) ≤
      (⨆ i, c i) * hausdorffEdist A B := by
    have h₁ : ∀ i, hausdorffEdist (f i '' A) (f i '' B) ≤
        (c i) * hausdorffEdist A B := by
      intro i
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε hci
      apply hausdorffEdist_le_of_mem_edist
      · intro x hx
        have h₁a : ∀ ε : NNReal, 0 < ε → hausdorffEdist (f i '' A) (f i '' B) ≤
            (c i) * hausdorffEdist A B + ε := by
          intro ε hε
          sorry

        have h₁b : ∃ y ∈ f i '' B,
            edist x y < (c i) * hausdorffEdist A B + ε := by
          sorry
        have h₁b' : ∃ y ∈ f i '' B,
            edist x y ≤ (c i) * hausdorffEdist A B + ε := by
          rcases h₁b with ⟨y, hy, hxy⟩
          use y
          constructor
          · exact hy
          · exact le_of_lt hxy
        exact h₁b'
      · sorry -- This is same as first part.

    -- we take this outside since we use it twice
    have hci : ∀ i, c i ≤ ⨆ i, c i := by
      intro i
      refine le_ciSup ?_ i
      simp_all only [Finite.bddAbove_range]

    -- supremum of the c i is greater than or equal to each c i, of course
    have h₂ : ∀ i, (c i) * hausdorffEdist A B ≤
        (⨆ i, c i) * hausdorffEdist A B := by
      intro i
      have h₁b₂ : hausdorffEdist A B ≤ hausdorffEdist A B := le_rfl -- this is a bit sus
      refine mul_le_mul ?_ h₁b₂ ?_ ?_
      specialize hci i
      · exact coe_le_coe.mpr hci
      · exact zero_le (hausdorffEdist A B)
      · simp_all only [le_refl, zero_le]

    simp only [iSup_le_iff]
    intro i
    specialize h₁ i
    specialize hci i
    have h₃ : (c i) * hausdorffEdist A B ≤ (⨆ i, c i) * hausdorffEdist A B := by
      simp_all
    exact le_trans h₁ h₃
  exact le_trans h h'


end attractor_uniq -- close the namespace
