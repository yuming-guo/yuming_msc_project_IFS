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

* `compact_exists_edist_le_of_hausdorffEdist_le`: If `x` is in a set `s`, and `t` is a nonempty
  compact set, and the Hausdorff distance between `s` and `t` is bounded by `r`, then there exists
  a point `y` in `t` such that the distance from `x` to `y` is at most `r`. This is an extention of
  the `exists_edist_lt_of_hausdorffEdist_lt` lemma, which proves only the less than case, without
  requiring compactness of `t`.

* `lipschitzonwith_maps_compact_to_compact`: If `f` is a Lipschitz map on a compact set `S`, then it
  maps a compact set `A` to a compact set `f '' A`.

* `lipschitz_restricts_hausdorff_dist`: If `f` is a Lipschitz map on a set `s`, then it restricts
  the Hausdorff distance between two sets `t` and `u` by a factor of the Lipschitz constant of `f`.

* `contr_maps_bounded_to_bounded`: If `f` is a contraction mapping, then it maps bounded sets to
  bounded sets.

* `dist_union_le_max_dist_ind`: Let `S` be the union of the images of sets `A` and `B` under a
  family of contraction mappings `f i`, then the Hausdorff distance between `S(A)` and `S(B)` is
  bounded by the maximum Hausdorff distance between the images of `A` and `B` under each `f i`.

* `union_of_lipschitz_contracts`: If `S` is the union of the images of sets `A` and `B` under a
  family of contraction mappings `f i`, then the Hausdorff distance between `S(A)` and `S(B)` is
  bounded by the supremum of the individual lipschitz constants multiplied by the Hausdorff distance
  between `A` and `B`.

* `attractor_uniq`: The main theorem that states the uniqueness of the attractor of an IFS. It
  states that there exists a unique set `A` such that `S(A) = A`, where `S` is the union of
  the images of sets under a family of contraction mappings `f i`.

# References
* [1] Kenneth Falconer, "Fractal Geometry: Mathematical Foundations and Applications", Wiley, 2003.
-/



open Bornology Metric ENNReal EMetric IsCompact

namespace theorem_91 -- sets up the namespace


/- This is the lemma that, in ENNReals, if b is non-infinity and a > 0, then b ≤ c implies b < c + a.
To be added into mathlib. -/
theorem ENNReal_lt_add_of_le_of_pos {a b c : ENNReal} (ha : a ≠ 0) (hb : b ≠ ⊤) (hbc : b ≤ c) :
    b < c + a := by
  obtain rfl | hbc := eq_or_lt_of_le hbc
  · exact lt_add_right hb ha
  exact lt_add_of_lt_of_nonneg hbc (zero_le _)


-- here we prove the LipschitzWith.weaken lemma, except for LipschitzOnWith
theorem LipschitzOnWith_Weaken {α : Type} {β : Type} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {s : Set α} {K K' : NNReal} {f : α → β} (hf : LipschitzOnWith K f s) (hK : K ≤ K') :
      LipschitzOnWith K' f s := by
  delta LipschitzOnWith at *
  intro x hx y hy
  have h1 : K * edist x y ≤ K' * edist x y := by gcongr -- le_implies_mul_le hK
  exact Preorder.le_trans (edist (f x) (f y)) (↑K * edist x y) (↑K' * edist x y) (hf hx hy) h1


/- this is the lemma that, if x is in s, and t is a nonempty compact set, and the Hausdorff distance
between s and t is bounded by r, then there exists a point y in t such that the distance from x to y
is at most r. This is an extention of the `exists_edist_lt_of_hausdorffEdist_lt` lemma, which proves
only the less than case, without requiring compactness of t. -/
theorem compact_exists_edist_le_of_hausdorffEdist_le {α : Type} [PseudoEMetricSpace α]
    {x : α} {s t : Set α} {r : ℝ≥0∞} (hx : x ∈ s) (ht : t.Nonempty)
    (H : hausdorffEdist s t ≤ r) (htc : IsCompact t) : ∃ y ∈ t, edist x y ≤ r := by
    have h₁ : infEdist x t ≤ r := by
      have h₁' : infEdist x t ≤ hausdorffEdist s t := infEdist_le_hausdorffEdist_of_mem hx
      exact le_trans h₁' H
    have h₂ : ∃ y ∈ t, infEdist x t = edist x y := exists_infEdist_eq_edist htc ht x
    -- bhavik pointed this lemma out
    obtain ⟨y, hy, hxy⟩ := h₂
    rw [hxy] at h₁
    use y


/- this is the lemma that, if f is a Lipschitz map on a compact set S, then it maps a compact set A
to a compact sets f '' A. -/
theorem lipschitzonwith_maps_compact_to_compact {α : Type} {β : Type} [PseudoEMetricSpace α]
    [PseudoEMetricSpace β] (S : Set α) (f : α → β) (K : NNReal) (hf : LipschitzOnWith K f S) :
    ∀ A ⊆ S, IsCompact A → IsCompact (f '' A) := by
  intro A hAD hA
  -- we use the fact that compactness is preserved under continuous maps
  refine IsCompact.image_of_continuousOn hA ?_
  have hf₁ : ContinuousOn f S := LipschitzOnWith.continuousOn hf
  have hf₂ : ContinuousOn f A := ContinuousOn.mono hf₁ hAD
  exact hf₂


/- this is the lemma that, if f is a Lipschitz map on a set s, then it restricts the Hausdorff
distance between two sets t and u by a factor of the lipschitz constant of f. -/
theorem lipschitz_restricts_hausdorff_dist {α : Type} [PseudoEMetricSpace α] {D s t : Set α}
    {f : α → α} {K : NNReal} (hs : s ⊆ D) (ht : t ⊆ D) (hsn : Nonempty s) (htn : Nonempty t)
    (hsc : IsCompact s) (htc : IsCompact t) (hf : LipschitzOnWith K f D) :
    hausdorffEdist (f '' s) (f '' t) ≤ K * hausdorffEdist s t := by
  -- first use directly lipschitz
  have h : ∀ x ∈ D, ∀ y ∈ D, edist (f x) (f y) ≤ K * edist x y := by
    intro x hx y hy
    delta LipschitzOnWith at hf
    specialize hf hx hy
    exact hf

  apply hausdorffEdist_le_of_mem_edist
  · have h₁ : ∀ m ∈ s, ∃ n ∈ t, edist (f m) (f n) ≤ K * hausdorffEdist s t := by
      intro m hm
      have h₁' : ∀ m ∈ s, ∃ n ∈ t, edist m n ≤ hausdorffEdist s t := by
        intro m hm
        refine compact_exists_edist_le_of_hausdorffEdist_le hm (Set.Nonempty.of_subtype)
            (Preorder.le_refl (hausdorffEdist s t)) htc
      specialize h₁' m hm
      cases' h₁' with n hn
      have hmD : m ∈ D := hs hm
      obtain ⟨hnt, hmn⟩ := hn
      have hnD : n ∈ D := ht hnt
      specialize h m hmD n hnD
      use n
      constructor
      · exact hnt
      · exact LipschitzOnWith.edist_le_mul_of_le hf (hs hm) (ht hnt) hmn

    -- this bit was an aesop
    intro x a
    simp_all only [nonempty_subtype, Set.mem_image, exists_exists_and_eq_and]
    obtain ⟨w, h_1⟩ := hsn
    obtain ⟨w_1, h_2⟩ := htn
    obtain ⟨w_2, h_3⟩ := a
    obtain ⟨left, right⟩ := h_3
    subst right
    simp_all only

  · have h₁ : ∀ m ∈ t, ∃ n ∈ s, edist (f m) (f n) ≤ K * hausdorffEdist t s := by
      intro m hm
      have h₁' : ∀ m ∈ t, ∃ n ∈ s, edist m n ≤ hausdorffEdist t s := by
        intro m hm
        refine compact_exists_edist_le_of_hausdorffEdist_le hm (Set.Nonempty.of_subtype)
            (Preorder.le_refl (hausdorffEdist t s)) hsc
      specialize h₁' m hm
      cases' h₁' with n hn
      have hmD : m ∈ D := ht hm
      obtain ⟨hnt, hmn⟩ := hn
      have hnD : n ∈ D := hs hnt
      specialize h m hmD n hnD
      use n
      constructor
      · exact hnt
      · exact LipschitzOnWith.edist_le_mul_of_le hf (ht hm) (hs hnt) hmn

    have hst : hausdorffEdist s t = hausdorffEdist t s := hausdorffEdist_comm
    aesop -- same aesop as above, not expanded here




/- Define some variables: D ∈ ℝ^n, define c and f, indexed by ι - f i corresponds to the individual
S_is in the informal proof, c i corresponds to each indiviual c_is, the factors in the contraction.
Finally we define S to be the union of all S_is. -/
variable {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))} {ι : Type*} (c : ι → NNReal)
  (i : ι) {f : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (ε : ENNReal)
  (x : EuclideanSpace ℝ (Fin n)) {S : Set (EuclideanSpace ℝ (Fin n)) → Set (EuclideanSpace ℝ (Fin n))}


-- this is the lemma that contractions map bounded sets to bounded sets
theorem contr_maps_bounded_to_bounded (hc : ∀ i, c i < 1)
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
theorem dist_union_le_sup_ind_dist (hD : IsCompact D)
    (hS : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsCompact A → S A = ⋃ i, (f i '' A))
    (hSi : ∀ i, LipschitzOnWith (c i) (f i) D):
    ∀ A B, A.Nonempty → B.Nonempty → IsCompact A → IsCompact B → A ⊆ D → B ⊆ D →
      hausdorffEdist (S A) (S B) ≤ ⨆ i, hausdorffEdist (f i '' A) (f i '' B) := by
  have hD' : IsBounded D := IsCompact.isBounded hD
  intro A B hAn hBn hAc hBc hAD hBD
  apply hausdorffEdist_le_of_mem_edist

  · intro x hx
    rw [hS] at hx
    · simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hx⟩ := hx
      have h₁ : hausdorffEdist (f i '' A) (f i '' B)
          ≤ ⨆ i, hausdorffEdist (f i '' A) (f i '' B) := le_iSup_iff.mpr fun b a => a i
      have h₂ : ∃ y ∈ f i '' B, edist x y ≤ ⨆ i, hausdorffEdist (f i '' A) (f i '' B) :=
          compact_exists_edist_le_of_hausdorffEdist_le hx (Set.Nonempty.image (f i) hBn) h₁
          (lipschitzonwith_maps_compact_to_compact D (f i) (c i) (hSi i) B hBD hBc)
      obtain ⟨y, hy, hxy⟩ := h₂
      have h₃ : y ∈ S B := by
        have h₃' : (f i '' B) ⊆ S B := by
          rw [hS]
          · exact Set.subset_iUnion_of_subset i fun ⦃a⦄ a => a
          · exact hBc
        exact h₃' hy
      use y
    · exact hAc

  · intro x hx
    rw [hS] at hx
    · simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hx⟩ := hx
      have h₁ : hausdorffEdist (f i '' B) (f i '' A)
          ≤ ⨆ i, hausdorffEdist (f i '' B) (f i '' A) := le_iSup_iff.mpr fun b a => a i
      have h₂ : ∃ y ∈ f i '' A, edist x y ≤ ⨆ i, hausdorffEdist (f i '' B) (f i '' A) :=
          compact_exists_edist_le_of_hausdorffEdist_le hx (Set.Nonempty.image (f i) hAn) h₁
          (lipschitzonwith_maps_compact_to_compact D (f i) (c i) (hSi i) A hAD hAc)
      have h₃ : ⨆ i, hausdorffEdist (f i '' B) (f i '' A) =
          ⨆ i, hausdorffEdist (f i '' A) (f i '' B) := by
        have h₃' : ∀ i, hausdorffEdist (f i '' B) (f i '' A) =
            hausdorffEdist (f i '' A) (f i '' B) := by
          intro i
          exact hausdorffEdist_comm
        exact iSup_congr h₃'
      rw [h₃] at h₂
      obtain ⟨y, hy, hxy⟩ := h₂

      have h₄ : y ∈ S A := by
        have h₃' : (f i '' A) ⊆ S A := by
          rw [hS]
          · exact Set.subset_iUnion_of_subset i fun ⦃a⦄ a => a
          · exact hAc
        exact h₃' hy
      use y
    · exact hBc


-- now we move on to proving [1][p.125, equation 9.5], i.e. the union of the contractions has
-- lipschitz constant at most the supremum of the individual lipschitz constants
theorem union_of_lipschitz_contracts (hD : IsCompact D)
    (hS : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsCompact A → S A = ⋃ i, (f i '' A))
    (hc : ∀ i, c i < 1) (hSi : ∀ i, LipschitzOnWith (c i) (f i) D):
    ∀ A B, A.Nonempty → B.Nonempty → IsCompact A → IsCompact B → A ⊆ D → B ⊆ D →
      hausdorffEdist (S A) (S B) ≤ (⨆ i, c i) * hausdorffEdist A B := by
  intro A B hAn hBn hAc hBc hAD hBD

  -- we begin by applying the previous lemma
  have h : hausdorffEdist (S A) (S B) ≤
      (⨆ i, hausdorffEdist (f i '' A) (f i '' B)) := by
    exact dist_union_le_sup_ind_dist c hD hS hSi A B hAn hBn hAc hBc hAD hBD

  have h' : ⨆ i, hausdorffEdist (f i '' A) (f i '' B) ≤
      (⨆ i, c i) * hausdorffEdist A B := by

    have h₁ : ∀ i, hausdorffEdist (f i '' A) (f i '' B) ≤
        (c i) * hausdorffEdist A B := by
      intro i
      apply hausdorffEdist_le_of_mem_edist
      · intro x hx
        have h₁a : hausdorffEdist (f i '' A) (f i '' B) ≤ ↑(c i) * hausdorffEdist A B := by
          specialize hSi i
          refine lipschitz_restricts_hausdorff_dist hAD hBD (Set.Nonempty.to_subtype hAn)
              (Set.Nonempty.to_subtype hBn) hAc hBc hSi
        have h₁b : IsCompact (f i '' B) := by
          specialize hSi i
          have h₁' : ∀ B ⊆ D, IsCompact B → IsCompact (f i '' B) :=
          lipschitzonwith_maps_compact_to_compact D (f i) (c i) hSi
          specialize h₁' B hBD hBc
          exact h₁'
        exact compact_exists_edist_le_of_hausdorffEdist_le hx (Set.Nonempty.image (f i) hBn) h₁a h₁b
      · intro x hx
        have h₁a : hausdorffEdist (f i '' B) (f i '' A) ≤ ↑(c i) * hausdorffEdist B A := by
          specialize hSi i
          exact lipschitz_restricts_hausdorff_dist hBD hAD (Set.Nonempty.to_subtype hBn)
              (Set.Nonempty.to_subtype hAn) hBc hAc hSi
        have h₁b : IsCompact (f i '' A) := by
          specialize hSi i
          have h₁' : ∀ A ⊆ D, IsCompact A → IsCompact (f i '' A) :=
          lipschitzonwith_maps_compact_to_compact D (f i) (c i) hSi
          specialize h₁' A hAD hAc
          exact h₁'
        have h₁c : ↑(c i) * hausdorffEdist A B = ↑(c i) * hausdorffEdist B A := by
          have h₁c' : hausdorffEdist A B = hausdorffEdist B A := hausdorffEdist_comm
          rw [h₁c']
        have h₁a' : hausdorffEdist (f i '' B) (f i '' A) ≤ ↑(c i) * hausdorffEdist A B := by
          rw [h₁c]
          exact h₁a
        exact compact_exists_edist_le_of_hausdorffEdist_le hx (Set.Nonempty.image (f i) hAn) h₁a' h₁b

    -- we take this outside since we use it twice
    have hci : ∀ i, c i ≤ ⨆ i, c i := by
      intro i
      refine le_ciSup ?_ i
      use 1
      rw [mem_upperBounds]

      -- this aesop is by BM
      intro x a
      simp_all only [Set.mem_range]
      obtain ⟨w, h_1⟩ := a
      subst h_1
      apply le_of_lt
      simp_all only

    -- supremum of the c i is greater than or equal to each c i, of course
    have h₂ : ∀ i, (c i) * hausdorffEdist A B ≤ (⨆ i, c i) * hausdorffEdist A B := by
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


theorem attractor_uniq (hD : IsCompact D)
    (hS : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsCompact A → S A = ⋃ i, (f i '' A))
    (hc : ∀ i, c i < 1) (hSi : ∀ i, LipschitzOnWith (c i) (f i) D) [Fintype ι] :
    ∃! A ⊆ D, S A = A := by
  have h1 : ∀ A B, A.Nonempty → B.Nonempty → IsCompact A → IsCompact B → A ⊆ D → B ⊆ D → hausdorffEdist (S A) (S B)
      ≤ ⨆ i, hausdorffEdist (f i '' A) (f i '' B) := dist_union_le_sup_ind_dist c hD hS hSi

  let f' : ι → D → D := fun i x => ⟨f i x, by
    -- need to show that f i x ∈ D
    sorry
  ⟩

  let S' : Set D → Set D := fun A => S A, by
    sorry



  have h2 : ContractingWith (⨆ i, c i) S' := by
    -- need to show that S' is contracting with the c i
    sorry
  sorry

end theorem_91 -- close the namespace
