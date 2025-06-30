-- import Mathlib.Analysis.InnerProductSpace.PiL2
-- import Mathlib.Order.CompletePartialOrder
import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniness of the Attractor of an IFS

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
* `dist_union_le_max_dist_ind`: Let `S` be the union of the images of a set `A` under a family of
  contraction mappings `f i`, then the Hausdorff distance between `S A` and `S B` is bounded by the
  maximum Hausdorff distance between the images of `A` and `B` under each `f i`.
-/
open Bornology Metric ENNReal EMetric

namespace coursework2 -- sets up the namespace


/- This is the lemma that, in ENNReals, if b is non-infinity and a > 0, then b ≤ c implies b < c + a.
To be added into mathlib. -/
lemma lt_add_of_le_of_pos_ENNReal {a b c : ENNReal} (ha : a ≠ 0) (hb : b ≠ ⊤) (hbc : b ≤ c) :
    b < c + a := by
  obtain rfl | hbc := eq_or_lt_of_le hbc
  · exact lt_add_right hb ha
  exact lt_add_of_lt_of_nonneg hbc (zero_le _)


lemma le_of_forall_pos_lt_add_ENNReal {a b : ENNReal}
    (h : ∀ ε : ENNReal, 0 < ε → a < b + ε) : a ≤ b := by
    have h' : ∀ ε : ENNReal, 0 < ε → a ≤ b + ε := by
      intro ε hε
      specialize h ε hε
      exact le_of_lt h
    exact _root_.le_of_forall_pos_le_add h'


-- here we prove the LipschitzWith.weaken lemma, except for LipschitzOnWith
lemma LipschitzOnWith_Weaken {α : Type} {β : Type} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
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
theorem dist_union_le_max_dist_ind (hfi : ∀ i, Set.MapsTo (f i) D D) (hD : IsCompact D)
    (hS : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsCompact A → S A = ⋃ i, (f i '' A))
    (hc : ∀ i, c i < 1) (hSi : ∀ i, LipschitzOnWith (c i) (f i) D) (δ : ENNReal):
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
            exact contr_maps_bounded_to_bounded n c i hc hSi A hAD h1ba -- this is a lemma to be proven
          · have h1bb : IsBounded B := IsBounded.subset hD' hBD
            exact contr_maps_bounded_to_bounded n c i hc hSi B hBD h1bb -- same as above
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
          have h2b' : (f i '' B) ⊆ S B := by
            rw [hS]
            · exact Set.subset_iUnion_of_subset i fun ⦃a⦄ a => a
            · exact hBc
          exact h2b' hy
        use y

      obtain ⟨y, hy, hy'⟩ := h2 ε (by simpa)
      exact ⟨y, hy, hy'.le⟩
    · exact hAc -- we have from the definition that A is compact
  · sorry  -- this one is the same as the 1st goal, just different order of A and B
