import Mathlib.Tactic -- imports all the lean tactics
import Mathlib.MeasureTheory.Measure.Hausdorff -- imports the Hausdorff measure
import Mathlib.Topology.MetricSpace.HausdorffDimension -- imports the Hausdorff dimension
import Mathlib.Order.CompletePartialOrder -- imports the definition of complete partial order

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Mass Distribution Principle

This file contains the formalisation of the Mass Distribution Principle, which is a fundamental
result in geometric measure theory. It states that if a mass distribution on a set satisfies
certain conditions, then the Hausdorff measure of that set is bounded below by a function of the
mass distribution and the dimension of the set. See [1] p.60, 'Mass distribution principle 4.2'.

# Main Results

* `mass_dist_principle`: If μ is a mass distribution on F, any subset of a space, and suppose
that for some s there exist numbers c, ε > 0, such that μ(U) ≤ c|U|^s for all sets U with |U| ≤ ε.
Then Hˢ(F) ≥ μ(F)/c.
* `mass_dist_principle_dimH`: As a direct consequence of the previous theorem, we have dim_H(F) ≥ s.

# References

* [1] Kenneth Falconer, "Fractal Geometry: Mathematical Foundations and Applications"
-/

open ENNReal MeasureTheory EMetric

namespace mdp -- sets up the namespace

/- Let X be a measurable space; c and ε positive real numbers (formatted as NNReals), s a non-neg
real number, and μ a mass distribution on F. -/
variable {X : Type*} [MeasurableSpace X] {ε : ENNReal} {c : NNReal} (s : NNReal) (μ : Measure X)

/- Let X be a metric space, Borel space and measure space. Let F be a subset of X. We have that for
all sets U in X, if |U| ≤ ε, then μ(U) ≤ c|U|^s. Then the mass distribution principle states that
the s-dimensional Hausdorff measure of F is greater or equal to μ(F) / c. -/
theorem mass_dist_principle [MetricSpace X] [BorelSpace X] (hε : 0 < ε) (F : Set X) (hs: 0 < s)
    (hμ : ∀ U : Set X, diam U ≤ ε → μ U ≤ c * diam U ^ NNReal.toReal s) : μ F / c ≤ μH[s] F := by
  rw [Measure.hausdorffMeasure_apply] /- Then we apply the definition of s-dimensional Hausdorff
  measure -/
  apply le_iSup₂_of_le ε hε /- This is the proof that the lower bound of function value implies
  lower bound of indexed supremum in complete lattices (which ENNReal is) with double indices -/
  refine le_iInf₂ fun U hU => ?_

  refine le_iInf fun hU' => ?_
  -- Here we prove the string of inequalities 0 < μ(F) ≤ μ(∪U_i) ≤ Σμ(U_i) ≤ cΣ|U_i|^s
  have h1 : μ F ≤ c * ∑' n, diam (U n) ^ NNReal.toReal s := calc
    _ ≤ μ (⋃ n, U n) := measure_mono hU
    _ ≤ ∑' n, μ (U n) := measure_iUnion_le U
    _ ≤ c * ∑' n, diam (U n) ^ NNReal.toReal s := by
      rw [← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum fun a => hμ _ (hU' a)

  -- Now we can divide both sides by c
  have h2 : μ F / c ≤ ∑' n, diam (U n) ^ NNReal.toReal s := div_le_of_le_mul' h1

  /- Now we prove that the sum of the sth powers of the diameters of the components of the cover is
  less than or equal to the sum of the supremums of the sth powers of the diameters of the components -/
  have h3 : ∑' (n : ℕ), diam (U n) ^ NNReal.toReal s ≤
      ∑' (n : ℕ), ⨆ (_ : (U n).Nonempty), diam (U n) ^ NNReal.toReal s := by
    gcongr with n
    rcases (U n).eq_empty_or_nonempty with hE | hNE
    -- However, if the component is empty:
    · simpa [hE] -- Converts the goal to 0 < s
    · simp [hNE] -- This then simply converts the goal to 0 < s

  -- Then the result follows by the transitivity of inequalities
  exact le_trans h2 h3


/- Then as a direct consequence, we have dim_H(F) ≥ s. Note that here we have to convert dimH
from ENNReal to NNReal to allow for the comparison with s. -/
theorem mass_dist_principle_dimH [MetricSpace X] [BorelSpace X] (F : Set X) (hμ' : μ F ≠ 0)
    (hε : 0 < ε) (hs : 0 ≤ s)
    (hμ : ∀ U : Set X, EMetric.diam U ≤ ε → μ U ≤ c * EMetric.diam U ^ NNReal.toReal s):
    s ≤ dimH F := by
  -- First we establish the trivial result that μ(F) / c > 0
  obtain rfl | hs' := hs.eq_or_lt
  · simp
  have h1 : 0 < μ F / c := ENNReal.div_pos hμ' (by simp)

  -- Now we apply the mass distribution principle to get H^s(F) ≥ μ(F) / c
  have h2 : μ F / c ≤ μH[s] F := by simpa [hs] using mass_dist_principle s μ hε F hs' hμ

  /- This then implies that H^s(F) > 0. Here we use H^s(F) ≠ 0 since that is the required
  input for the theorem proving dimH(F) ≥ s in mathlib -/
  have h3 : μH[s] F ≠ 0 := (h1.trans_le h2).ne'

  -- then if s-dim Hausdorff measure is positive, the Hausdorff dimension is greater or equal to s
  exact le_dimH_of_hausdorffMeasure_ne_zero h3

end mdp -- closes the namespace
