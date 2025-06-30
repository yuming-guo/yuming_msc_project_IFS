import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Iterated Function Systems
(Bit of an alternative definition of IFS, not sure if that would be a great idea)
-/

-- let X be a complete metric space
variable {X : Type*} [MetricSpace X] [CompleteSpace X]

-- define a contraction map on X
structure contraction (X : Type*) [MetricSpace X] where
  (f : X -> X)
  (lipschitz : ContractingWith 1 f)

-- define an iterated function system (IFS) as a finite set of contractions
structure IFS (X : Type*) [MetricSpace X] where
  (f : Finset (contraction X))
