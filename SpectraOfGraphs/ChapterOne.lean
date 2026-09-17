import SpectraOfGraphs.Basic
import Mathlib

namespace SpectraOfGraphs
/- # 1.1 Matrices associated to a graph -/
variable {V : Type*} [Fintype V] [DecidableEq V]

--x^TLx = 1/2 sum_{i,j} A_{ij}(x_i-x_j)^2
theorem laplacian_quadForm (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
  x ⬝ᵥ (lapMatrix G).mulVec x = ∑ i, ∑ j, adjMatrix G i j * (x i - x j)^2 / 2 := by
    simp only [sub_sq]
    have expand : ∀ v u : V, adjMatrix G v u * (x v ^ 2 - 2 * x v * x u + x u ^ 2) / 2 =
    adjMatrix G v u * x v ^ 2 / 2 - adjMatrix G v u * x v * x u + adjMatrix G v u * x u ^ 2 / 2
    := by
      intro v u
      ring_nf
    simp_rw [expand]
    simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    simp_rw [adjMatrix_row_sum]
    rw [Finset.sum_comm (f := fun i j => adjMatrix G i j * x j ^ 2)]
    simp_rw [adjMatrix_symmetric]
    simp_rw [← Finset.sum_mul, adjMatrix_row_sum]
    ring_nf
    unfold lapMatrix
    simp only [dotProduct, Matrix.mulVec, Matrix.sub_apply, Finset.mul_sum]
    simp_rw [sub_mul, mul_sub]
    ring_nf
    simp_rw [Finset.sum_sub_distrib]
    unfold degMatrix
    simp only [Matrix.of_apply]
    simp_rw [mul_ite, mul_zero, ite_mul, zero_mul]
    simp [Finset.sum_ite_eq]
    ring_nf
    simp_rw [mul_comm, <- mul_assoc, mul_comm]

--x^TQx = 1/2 sum_{i,j} A_{ij}(x_i-x_j)^2
theorem s_laplacian_quadForm (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
  x ⬝ᵥ (sLapMatrix G).mulVec x = ∑ i, ∑ j, adjMatrix G i j * (x i + x j)^2 / 2 := by
    simp only [add_sq]
    have expand : ∀ v u : V, adjMatrix G v u * (x v ^ 2 + 2 * x v * x u + x u ^ 2) / 2 =
    adjMatrix G v u * x v ^ 2 / 2 + adjMatrix G v u * x v * x u + adjMatrix G v u * x u ^ 2 / 2
    := by
      intro v u
      ring_nf
    simp_rw [expand]
    simp_rw [Finset.sum_add_distrib]
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    simp_rw [adjMatrix_row_sum]
    rw [Finset.sum_comm (f := fun i j => adjMatrix G i j * x j ^ 2)]
    simp_rw [adjMatrix_symmetric]
    simp_rw [← Finset.sum_mul, adjMatrix_row_sum]
    ring_nf
    unfold sLapMatrix
    simp only [dotProduct, Matrix.mulVec, Matrix.add_apply, Finset.mul_sum]
    simp_rw [add_mul, mul_add]
    ring_nf
    simp_rw [Finset.sum_add_distrib]
    unfold degMatrix
    simp only [Matrix.of_apply]
    simp_rw [mul_ite, mul_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring_nf
    simp_rw [mul_comm, <- mul_assoc, mul_comm]

theorem laplacian_positive_semidefinite (G : SimpleGraph V) [DecidableRel G.Adj] :
  Matrix.PosSemidef (lapMatrix G) := by
    constructor
    · simp [Matrix.IsSymm, Matrix.transpose] -- symmetric
      simp [lapMatrix_symmetric]
      rfl
    · intro x -- non-negative
      simp only [star_trivial, mul_zero, implies_true, Finsupp.sum_fintype, zero_mul, Finset.sum_const_zero]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      change 0 ≤ x ⬝ᵥ (lapMatrix G).mulVec x
      rw [laplacian_quadForm]
      apply Finset.sum_nonneg
      intro v _
      apply Finset.sum_nonneg
      intro u _
      simp_rw [adjMatrix, Matrix.of_apply]
      by_cases h: G.Adj u v
      · positivity
      · positivity

theorem s_laplacian_positive_semidefinite (G : SimpleGraph V) [DecidableRel G.Adj] :
  Matrix.PosSemidef (sLapMatrix G) := by
    constructor
    · simp [Matrix.IsSymm, Matrix.transpose] -- symmetric
      simp [sLapMatrix_symmetric]
      rfl
    · intro x -- non-negative
      simp only [star_trivial, mul_zero, implies_true, Finsupp.sum_fintype, zero_mul, Finset.sum_const_zero]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      change 0 ≤ x ⬝ᵥ (sLapMatrix G).mulVec x
      rw [s_laplacian_quadForm]
      apply Finset.sum_nonneg
      intro v _
      apply Finset.sum_nonneg
      intro u _
      simp_rw [adjMatrix, Matrix.of_apply]
      by_cases h: G.Adj u v
      · positivity
      · positivity




/- # 1.2 The Spectrum of a graph-/


end SpectraOfGraphs
