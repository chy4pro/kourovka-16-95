import K1695.CyclicToMinpoly

open scoped Matrix BigOperators

namespace K1695

open Matrix

variable {K : Type*} [Field K]

/-- The square Krylov matrix with columns `b, M b, ..., M^(m-1) b`. -/
def krylovMatrix {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (b : Fin m → K) : Matrix (Fin m) (Fin m) K :=
  fun i j ↦ ((M ^ (j : ℕ)) *ᵥ b) i

/-- Coefficients of the unitriangular change of Krylov columns. -/
private def feedbackCoeff (a : ℕ → K) : ℕ → ℕ → K
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, 0 => a k
  | k + 1, r + 1 => feedbackCoeff a k r

@[simp]
private theorem feedbackCoeff_diag (a : ℕ → K) :
    ∀ k : ℕ, feedbackCoeff a k k = 1
  | 0 => rfl
  | k + 1 => feedbackCoeff_diag a k

private theorem feedbackCoeff_eq_zero_of_lt (a : ℕ → K)
    {k r : ℕ} (h : k < r) : feedbackCoeff a k r = 0 := by
  induction k generalizing r with
  | zero =>
      cases r with
      | zero => omega
      | succ r => rfl
  | succ k ih =>
      cases r with
      | zero => omega
      | succ r =>
          exact ih (by omega)

/-- **Feedback invariance.** A rank-one feedback `b ℓᵀ` changes each
Krylov column only by a linear combination of preceding columns, so the
Krylov determinant is unchanged. -/
theorem krylov_det_feedback {m : ℕ}
    (M : Matrix (Fin m) (Fin m) K) (b ℓ : Fin m → K) :
    (krylovMatrix (M + Matrix.vecMulVec b ℓ) b).det =
      (krylovMatrix M b).det := by
  classical
  let F : Matrix (Fin m) (Fin m) K := M + Matrix.vecMulVec b ℓ
  let z : ℕ → Fin m → K := fun k ↦ (F ^ k) *ᵥ b
  let u : ℕ → Fin m → K := fun k ↦ (M ^ k) *ᵥ b
  let a : ℕ → K := fun k ↦ ℓ ⬝ᵥ z k
  have hu0 : u 0 = b := by simp [u]
  have husucc (k : ℕ) : M *ᵥ u k = u (k + 1) := by
    simp [u, pow_succ', Matrix.mulVec_mulVec]
  have hzsucc (k : ℕ) : z (k + 1) = M *ᵥ z k + a k • b := by
    change (F ^ (k + 1)) *ᵥ b = M *ᵥ z k + a k • b
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    change (M + Matrix.vecMulVec b ℓ) *ᵥ z k = M *ᵥ z k + a k • b
    rw [Matrix.add_mulVec, Matrix.vecMulVec_mulVec]
    simp [a]
  have hrep : ∀ k : ℕ,
      z k = ∑ r ∈ Finset.range (k + 1), feedbackCoeff a k r • u r := by
    intro k
    induction k with
    | zero => simp [z, u, feedbackCoeff]
    | succ k ih =>
        rw [hzsucc, ih]
        change M.mulVecLin
            (∑ r ∈ Finset.range (k + 1), feedbackCoeff a k r • u r) +
            a k • b = _
        rw [map_sum]
        simp only [LinearMap.map_smul, Matrix.mulVecLin_apply, husucc]
        conv_rhs => rw [Finset.sum_range_succ']
        simp [feedbackCoeff, hu0]
  let U : Matrix (Fin m) (Fin m) K :=
    fun i j ↦ feedbackCoeff a (j : ℕ) (i : ℕ)
  have hmatrix : krylovMatrix F b = krylovMatrix M b * U := by
    ext i j
    have hjle : j.val + 1 ≤ m := Nat.succ_le_iff.mpr j.isLt
    have hsubset : Finset.range (j.val + 1) ⊆ Finset.range m :=
      Finset.range_mono hjle
    have hpad :
        (∑ r ∈ Finset.range (j.val + 1),
            feedbackCoeff a j.val r • u r) =
          ∑ r ∈ Finset.range m, feedbackCoeff a j.val r • u r := by
      apply Finset.sum_subset hsubset
      intro r hrm hrsmall
      have hjr : j.val < r := by
        have : ¬ r < j.val + 1 := by
          simpa only [Finset.mem_range] using hrsmall
        omega
      rw [feedbackCoeff_eq_zero_of_lt a hjr]
      simp
    calc
      krylovMatrix F b i j = z j.val i := rfl
      _ = (∑ r ∈ Finset.range (j.val + 1),
          feedbackCoeff a j.val r • u r) i := congrFun (hrep j.val) i
      _ = (∑ r ∈ Finset.range m,
          feedbackCoeff a j.val r • u r) i := congrFun hpad i
      _ = ∑ r ∈ Finset.range m,
          u r i * feedbackCoeff a j.val r := by
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            apply Finset.sum_congr rfl
            intro r _
            exact mul_comm _ _
      _ = ∑ r : Fin m, u r.val i * feedbackCoeff a j.val r.val := by
            exact (Fin.sum_univ_eq_sum_range
              (fun r ↦ u r i * feedbackCoeff a j.val r) m).symm
      _ = (krylovMatrix M b * U) i j := by
            rfl
  have hupper : U.IsUpperTriangular := by
    intro i j hji
    exact feedbackCoeff_eq_zero_of_lt a hji
  have hdetU : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hupper]
    simp [U]
  change (krylovMatrix F b).det = (krylovMatrix M b).det
  rw [hmatrix, Matrix.det_mul, hdetU, mul_one]

/-- **Exact dimension reduction.** Nonvanishing of the lower Krylov
determinant obtained by deleting coordinate `j` lifts to nonvanishing of the
full Krylov determinant based at the standard vector `e_j`. This is the
linear-algebra core of the `y_j = 0` deflation step. -/
theorem krylov_reduce_of_zero {m : ℕ}
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (j : Fin (m + 1))
    (hdet :
      (krylovMatrix (principalBlockExcept B j) (pivotColumnExcept B j)).det ≠ 0) :
    (krylovMatrix B (Pi.single j 1)).det ≠ 0 := by
  have hctrl : LinearIndependent K (fun k : Fin m ↦
      ((principalBlockExcept B j) ^ (k : ℕ)) *ᵥ pivotColumnExcept B j) := by
    have hcols := Matrix.linearIndependent_cols_of_det_ne_zero hdet
    change LinearIndependent K (fun k : Fin m ↦
      ((principalBlockExcept B j) ^ (k : ℕ)) *ᵥ pivotColumnExcept B j) at hcols
    exact hcols
  have hfull : LinearIndependent K (fun k : Fin (m + 1) ↦
      (B ^ (k : ℕ)) *ᵥ Pi.single j 1) := by
    simpa using
      (cyclic_standardBasis_of_principalBlock B (Equiv.refl _) j (by
        simpa using hctrl))
  have hcols : LinearIndependent K (krylovMatrix B (Pi.single j 1)).col := by
    change LinearIndependent K (fun k : Fin (m + 1) ↦
      (B ^ (k : ℕ)) *ᵥ Pi.single j 1)
    exact hfull
  have hunit : IsUnit (krylovMatrix B (Pi.single j 1)) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

#print axioms krylov_det_feedback
#print axioms krylov_reduce_of_zero

end K1695
