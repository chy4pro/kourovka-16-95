import Mathlib

open scoped Matrix

namespace K1695

open Matrix

variable {K : Type*} [Field K]
variable {n : ℕ}

/-- The vector e_a-e_b. -/
def transpositionVector (a b : Fin n) : Fin n → K :=
  Pi.single a 1 - Pi.single b 1

/-- The permutation matrix of the transposition (a b). -/
def transpositionMatrix (a b : Fin n) : Matrix (Fin n) (Fin n) K :=
  Matrix.swap K a b

/-- L1: the transposition matrix is one minus the outer product of d with itself. -/
theorem l1_matrix_identity (a b : Fin n) (hab : a ≠ b) :
    transpositionMatrix (K := K) a b =
      1 - Matrix.vecMulVec (transpositionVector (K := K) a b)
        (transpositionVector (K := K) a b) := by
  classical
  ext i j
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    by_cases hja : j = a <;> by_cases hjb : j = b <;>
    simp_all [transpositionMatrix, Matrix.swap, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Matrix.vecMulVec_apply,
      transpositionVector, Equiv.swap_apply_def, Matrix.one_apply, eq_comm]

/-- L1: a transposition matrix is an involution. -/
theorem l1_mul_self (a b : Fin n) (_hab : a ≠ b) :
    transpositionMatrix (K := K) a b * transpositionMatrix (K := K) a b = 1 := by
  simpa only [transpositionMatrix] using Matrix.swap_mul_self (R := K) a b

/-- L1: the inverse represented by the unit is the same transposition matrix. -/
theorem l1_unit_inv (a b : Fin n) (_hab : a ≠ b) :
    ((Matrix.GeneralLinearGroup.swap K a b)⁻¹ :
      Matrix.GeneralLinearGroup (Fin n) K) =
      Matrix.GeneralLinearGroup.swap K a b := by
  ext
  simp [Matrix.GeneralLinearGroup.swap]

/-- L1: matrix inversion also fixes the transposition matrix. -/
theorem l1_matrix_inv (a b : Fin n) (hab : a ≠ b) :
    (transpositionMatrix (K := K) a b)⁻¹ =
      transpositionMatrix (K := K) a b := by
  change ((↑(Matrix.GeneralLinearGroup.swap K a b) :
    Matrix (Fin n) (Fin n) K)⁻¹) =
      (↑(Matrix.GeneralLinearGroup.swap K a b) : Matrix (Fin n) (Fin n) K)
  rw [← Matrix.GeneralLinearGroup.coe_inv]
  exact congrArg Units.val (l1_unit_inv (K := K) a b hab)

/-- Right multiplication by the transposition matrix preserves rank. -/
theorem rank_mul_transposition (B : Matrix (Fin n) (Fin n) K)
    (a b : Fin n) (hab : a ≠ b) :
    (B * transpositionMatrix (K := K) a b).rank = B.rank := by
  apply le_antisymm
  · exact Matrix.rank_mul_le_left _ _
  · have h := Matrix.rank_mul_le_left
      (B * transpositionMatrix (K := K) a b)
      (transpositionMatrix (K := K) a b)
    simpa only [Matrix.mul_assoc, l1_mul_self a b hab, Matrix.mul_one] using h

/-- Scaling an outer product can be absorbed into its first vector. -/
theorem smul_vecMulVec (c : K) (x y : Fin n → K) :
    c • Matrix.vecMulVec x y = Matrix.vecMulVec (c • x) y := by
  ext i j
  simp [Matrix.vecMulVec_apply, mul_assoc]

/-- L2: rank identity for multiplication by a transposition. -/
theorem l2_rank_identity (A : Matrix (Fin n) (Fin n) K) (μ : K)
    (a b : Fin n) (hab : a ≠ b) :
    (A * transpositionMatrix (K := K) a b - μ • 1).rank =
      ((A - μ • 1) +
        μ • Matrix.vecMulVec (transpositionVector (K := K) a b)
          (transpositionVector (K := K) a b)).rank := by
  let P := transpositionMatrix (K := K) a b
  let d := transpositionVector (K := K) a b
  have hfactor : A * P - μ • 1 = (A - μ • P) * P := by
    rw [Matrix.sub_mul, Matrix.smul_mul, l1_mul_self a b hab]
  have hexpand : A - μ • P = (A - μ • 1) + μ • Matrix.vecMulVec d d := by
    rw [show P = 1 - Matrix.vecMulVec d d by
      simpa only [P, d] using l1_matrix_identity (K := K) a b hab]
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring
  calc
    (A * P - μ • 1).rank = ((A - μ • P) * P).rank := congrArg Matrix.rank hfactor
    _ = (A - μ • P).rank := rank_mul_transposition _ a b hab
    _ = ((A - μ • 1) + μ • Matrix.vecMulVec d d).rank :=
      congrArg Matrix.rank hexpand

/-- Rank is subadditive for matrices over a field. -/
theorem matrix_rank_add_le (E F : Matrix (Fin n) (Fin n) K) :
    (E + F).rank ≤ E.rank + F.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- L3: a rank-one update changes rank by at most one. -/
theorem l3_rank_one_update_bounds (E : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) :
    E.rank - 1 ≤ (E + Matrix.vecMulVec x y).rank ∧
      (E + Matrix.vecMulVec x y).rank ≤ E.rank + 1 := by
  let R := Matrix.vecMulVec x y
  have hR : R.rank ≤ 1 := by
    simpa only [R] using Matrix.rank_vecMulVec_le x y
  have hu : (E + R).rank ≤ E.rank + 1 :=
    (matrix_rank_add_le E R).trans (Nat.add_le_add_left hR E.rank)
  have hrestore : (E + R) + Matrix.vecMulVec (-x) y = E := by
    ext i j
    simp [R, Matrix.vecMulVec_apply]
  have hneg : (Matrix.vecMulVec (-x) y).rank ≤ 1 :=
    Matrix.rank_vecMulVec_le (-x) y
  have hb : E.rank ≤ (E + R).rank + 1 := by
    calc
      E.rank = ((E + R) + Matrix.vecMulVec (-x) y).rank :=
        congrArg Matrix.rank hrestore.symm
      _ ≤ (E + R).rank + (Matrix.vecMulVec (-x) y).rank :=
        matrix_rank_add_le _ _
      _ ≤ (E + R).rank + 1 := Nat.add_le_add_left hneg _
  constructor
  · change E.rank - 1 ≤ (E + R).rank
    exact Nat.sub_le_iff_le_add.mpr hb
  · exact hu

/-- A vector outside the row space detects a vector in the kernel. -/
theorem exists_ker_dotProduct_ne_zero_of_not_mem_range_transpose
    (E : Matrix (Fin n) (Fin n) K) (y : Fin n → K)
    (hy : y ∉ LinearMap.range E.transpose.mulVecLin) :
    ∃ z : Fin n → K, E.mulVecLin z = 0 ∧ dotProduct y z ≠ 0 := by
  classical
  let φ : Module.Dual K (Fin n → K) := dotProductBilin K K y
  have hφrange : φ ∉ LinearMap.range E.mulVecLin.dualMap := by
    intro hφ
    obtain ⟨ψ, hψ⟩ := hφ
    let u : Fin n → K := (Pi.basisFun K (Fin n)).dualBasis.equivFun ψ
    have hrepr : dotProductBilin K K u = ψ := by
      apply (Pi.basisFun K (Fin n)).ext
      intro i
      simp [u, dotProductBilin_apply_apply, dotProduct, Pi.single_apply,
        eq_comm]
    apply hy
    refine ⟨u, ?_⟩
    ext j
    have hj := LinearMap.congr_fun hψ (Pi.single j 1)
    rw [← hrepr] at hj
    simpa [φ, dotProductBilin_apply_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec, Matrix.vecMul_apply_eq_sum, dotProduct,
      Pi.single_apply] using hj
  have hφann : φ ∉ (LinearMap.ker E.mulVecLin).dualAnnihilator := by
    rwa [← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  rw [Submodule.mem_dualAnnihilator] at hφann
  push Not at hφann
  obtain ⟨z, hzker, hzφ⟩ := hφann
  exact ⟨z, by simpa only [LinearMap.mem_ker] using hzker, by simpa [φ] using hzφ⟩

/-- L6a: the exact rank increase for a transverse rank-one update. -/
theorem l6a_rank_one_update_eq_add_one (E : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K)
    (hx : x ∉ LinearMap.range E.mulVecLin)
    (hy : y ∉ LinearMap.range E.transpose.mulVecLin) :
    (E + Matrix.vecMulVec x y).rank = E.rank + 1 := by
  classical
  let U := E + Matrix.vecMulVec x y
  obtain ⟨z₀, hz₀E, hz₀dot⟩ :=
    exists_ker_dotProduct_ne_zero_of_not_mem_range_transpose E y hy
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply hx
    rw [hxzero]
    exact Submodule.zero_mem _
  have hker_le : LinearMap.ker U.mulVecLin ≤ LinearMap.ker E.mulVecLin := by
    intro z hzU
    rw [LinearMap.mem_ker] at hzU ⊢
    have hsum : E.mulVecLin z + (dotProduct y z) • x = 0 := by
      simpa [U, Matrix.mulVecLin_apply, Matrix.add_mulVec,
        Matrix.vecMulVec_mulVec] using hzU
    by_contra hEz
    have hdot : dotProduct y z ≠ 0 := by
      intro hzero
      rw [hzero, zero_smul, add_zero] at hsum
      exact hEz hsum
    apply hx
    refine ⟨(-(dotProduct y z))⁻¹ • z, ?_⟩
    rw [LinearMap.map_smul]
    have hE : E.mulVecLin z = -(dotProduct y z) • x := by
      simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hsum
    rw [hE, smul_smul]
    simp [hdot]
  have hz₀U : z₀ ∉ LinearMap.ker U.mulVecLin := by
    rw [LinearMap.mem_ker]
    have hz₀E' : E *ᵥ z₀ = 0 := hz₀E
    simp only [U, Matrix.mulVecLin_apply, Matrix.add_mulVec,
      Matrix.vecMulVec_mulVec]
    rw [hz₀E', zero_add, op_smul_eq_smul]
    exact smul_ne_zero hz₀dot hx0
  have hker_lt : LinearMap.ker U.mulVecLin < LinearMap.ker E.mulVecLin := by
    apply lt_of_le_of_ne hker_le
    intro heq
    apply hz₀U
    rw [heq]
    simpa only [LinearMap.mem_ker] using hz₀E
  have hfinrank_lt :
      Module.finrank K (LinearMap.ker U.mulVecLin) <
        Module.finrank K (LinearMap.ker E.mulVecLin) :=
    Submodule.finrank_lt_finrank_of_lt hker_lt
  have hnullE := E.mulVecLin.finrank_range_add_finrank_ker
  have hnullU := U.mulVecLin.finrank_range_add_finrank_ker
  have hnullE' : E.rank + Module.finrank K (LinearMap.ker E.mulVecLin) =
      Module.finrank K (Fin n → K) := by
    simpa only [Matrix.rank] using hnullE
  have hnullU' : U.rank + Module.finrank K (LinearMap.ker U.mulVecLin) =
      Module.finrank K (Fin n → K) := by
    simpa only [Matrix.rank] using hnullU
  have hrank_lt : E.rank < U.rank := by
    omega
  have hu := (l3_rank_one_update_bounds E x y).2
  change U.rank ≤ E.rank + 1 at hu
  change U.rank = E.rank + 1
  omega

/-- L6' (T2), with the necessary hypotheses `μ ≠ 0` and `2 ≤ n`. -/
theorem l6prime_t2_corrected (A : Matrix (Fin n) (Fin n) K) (μ : K)
    (a b : Fin n) (hab : a ≠ b) (hμ : μ ≠ 0) (hn : 2 ≤ n)
    (hrank : (A - μ • 1).rank = n - 2)
    (hcol : transpositionVector (K := K) a b ∉
      LinearMap.range (A - μ • 1).mulVecLin)
    (hrow : transpositionVector (K := K) a b ∉
      LinearMap.range (A - μ • 1).transpose.mulVecLin) :
    (A * transpositionMatrix (K := K) a b - μ • 1).rank = n - 1 := by
  let E := A - μ • 1
  let d := transpositionVector (K := K) a b
  have hμcol : μ • d ∉ LinearMap.range E.mulVecLin := by
    intro hmem
    apply hcol
    obtain ⟨v, hv⟩ := hmem
    refine ⟨μ⁻¹ • v, ?_⟩
    rw [LinearMap.map_smul, hv, smul_smul]
    simp [hμ, d]
  have hinc := l6a_rank_one_update_eq_add_one E (μ • d) d hμcol (by
    simpa only [E, d] using hrow)
  rw [← smul_vecMulVec] at hinc
  rw [l2_rank_identity A μ a b hab]
  change (E + μ • Matrix.vecMulVec d d).rank = n - 1
  have hrankE : E.rank = n - 2 := by simpa only [E] using hrank
  rw [hinc, hrankE]
  omega

/-- The coefficient comparison used in L7: `1` and a non-base-field element
are linearly independent over the base field. -/
theorem one_mu_coefficients_eq_zero {F L : Type*} [Field F] [Field L]
    [Algebra F L] (μ : L) (hμ : μ ∉ Set.range (algebraMap F L))
    (c₀ c₁ : F)
    (h : algebraMap F L c₀ + μ * algebraMap F L c₁ = 0) :
    c₀ = 0 ∧ c₁ = 0 := by
  have hc₁ : c₁ = 0 := by
    by_contra hc₁
    have hmapc₁ : algebraMap F L c₁ ≠ 0 :=
      (map_ne_zero (algebraMap F L)).2 hc₁
    apply hμ
    refine ⟨-c₀ / c₁, ?_⟩
    simp only [map_div₀, map_neg]
    rw [div_eq_iff hmapc₁]
    linear_combination -h
  subst c₁
  simp only [map_zero, mul_zero, add_zero] at h
  exact ⟨(FaithfulSMul.algebraMap_injective F L) (by simpa using h), rfl⟩

/-- L7 (T4), assuming the permitted coordinate decomposition
`z = z₀ + μ z₁` over the base field. -/
theorem l7_quadratic_descent_with_decomposition
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (A : Matrix (Fin n) (Fin n) F) (μ : L)
    (hμ : μ ∉ Set.range (algebraMap F L)) (s t : F)
    (hquad : μ * μ = algebraMap F L s + algebraMap F L t * μ)
    (w z₀ z₁ : Fin n → F) (z : Fin n → L)
    (hz : z = fun i => algebraMap F L (z₀ i) + μ * algebraMap F L (z₁ i))
    (heq : (A.map (algebraMap F L) - μ • 1).mulVec z =
      fun i => algebraMap F L (w i)) :
    ∃ z₁' : Fin n → F,
      w = (A * A - t • A - s • 1).mulVec z₁' := by
  classical
  let incl : (Fin n → F) → (Fin n → L) :=
    fun v i => algebraMap F L (v i)
  have hmap_mulVec (v : Fin n → F) :
      (A.map (algebraMap F L)).mulVec (incl v) = incl (A.mulVec v) := by
    ext i
    simp [incl, Matrix.mulVec, dotProduct, map_sum]
  have hz' : z = incl z₀ + μ • incl z₁ := by
    rw [hz]
    ext i
    simp [incl]
  have hexpand :
      (A.map (algebraMap F L) - μ • 1).mulVec z = fun i =>
        algebraMap F L ((A.mulVec z₀ - s • z₁) i) +
          μ * algebraMap F L ((A.mulVec z₁ - z₀ - t • z₁) i) := by
    rw [hz', Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.smul_mulVec, Matrix.one_mulVec, hmap_mulVec, hmap_mulVec]
    ext i
    simp [incl]
    rw [← mul_assoc μ μ (algebraMap F L (z₁ i)), hquad]
    ring
  have hcoeff (i : Fin n) :
      algebraMap F L ((A.mulVec z₀ - s • z₁ - w) i) +
        μ * algebraMap F L ((A.mulVec z₁ - z₀ - t • z₁) i) = 0 := by
    have hi := congrFun (hexpand.symm.trans heq) i
    simp only [Pi.sub_apply, Pi.smul_apply, RingHom.map_sub] at hi ⊢
    rw [← hi]
    ring
  have hbase : A.mulVec z₀ - s • z₁ - w = 0 := by
    ext i
    exact (one_mu_coefficients_eq_zero μ hμ _ _ (hcoeff i)).1
  have hlinear : A.mulVec z₁ - z₀ - t • z₁ = 0 := by
    ext i
    exact (one_mu_coefficients_eq_zero μ hμ _ _ (hcoeff i)).2
  have hw : w = A.mulVec z₀ - s • z₁ :=
    (sub_eq_zero.mp hbase).symm
  have hz₀ : z₀ = A.mulVec z₁ - t • z₁ := by
    funext i
    have hi := congrFun hlinear i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply] at hi
    simp only [Pi.sub_apply, Pi.smul_apply]
    change z₀ i = (A.mulVec z₁) i - t * z₁ i
    change (A.mulVec z₁) i - z₀ i - t * z₁ i = 0 at hi
    linear_combination -hi
  refine ⟨z₁, ?_⟩
  rw [hw, hz₀]
  ext i
  simp [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.smul_mulVec]


/-- L4 (T0): a transposition is derogatory only at an eigenvalue of A. -/
theorem l4_t0 (A : Matrix (Fin n) (Fin n) K) (μ : K)
    (a b : Fin n) (hab : a ≠ b)
    (hfull : (A - μ • 1).rank = n) :
    n - 1 ≤ (A * transpositionMatrix (K := K) a b - μ • 1).rank := by
  rw [l2_rank_identity A μ a b hab]
  have h := (l3_rank_one_update_bounds (A - μ • 1)
    (μ • transpositionVector (K := K) a b)
    (transpositionVector (K := K) a b)).1
  rw [← smul_vecMulVec] at h
  simpa only [hfull] using h

/-- Corrected L5: the natural-number formulation needs the explicit hypothesis 3 ≤ n. -/
theorem l5_t3_corrected (A : Matrix (Fin n) (Fin n) K) (μ : K)
    (a b : Fin n) (hab : a ≠ b) (hn : 3 ≤ n)
    (hsmall : (A - μ • 1).rank ≤ n - 3) :
    (A * transpositionMatrix (K := K) a b - μ • 1).rank ≤ n - 2 := by
  rw [l2_rank_identity A μ a b hab]
  have h := (l3_rank_one_update_bounds (A - μ • 1)
    (μ • transpositionVector (K := K) a b)
    (transpositionVector (K := K) a b)).2
  rw [← smul_vecMulVec] at h
  omega

section FourByFourExamples

variable (A E : Matrix (Fin 4) (Fin 4) K) (μ : K)
variable (a b : Fin 4) (hab : a ≠ b)
variable (x y : Fin 4 → K)

example :
    transpositionMatrix (K := K) a b =
      1 - Matrix.vecMulVec (transpositionVector (K := K) a b)
        (transpositionVector (K := K) a b) :=
  l1_matrix_identity a b hab

example :
    transpositionMatrix (K := K) a b * transpositionMatrix (K := K) a b = 1 :=
  l1_mul_self a b hab

example :
    (transpositionMatrix (K := K) a b)⁻¹ =
      transpositionMatrix (K := K) a b :=
  l1_matrix_inv a b hab

example :
    (A * transpositionMatrix (K := K) a b - μ • 1).rank =
      ((A - μ • 1) +
        μ • Matrix.vecMulVec (transpositionVector (K := K) a b)
          (transpositionVector (K := K) a b)).rank :=
  l2_rank_identity A μ a b hab

example :
    E.rank - 1 ≤ (E + Matrix.vecMulVec x y).rank ∧
      (E + Matrix.vecMulVec x y).rank ≤ E.rank + 1 :=
  l3_rank_one_update_bounds E x y

example (hfull : (A - μ • 1).rank = 4) :
    4 - 1 ≤ (A * transpositionMatrix (K := K) a b - μ • 1).rank :=
  l4_t0 A μ a b hab hfull

example (hsmall : (A - μ • 1).rank ≤ 4 - 3) :
    (A * transpositionMatrix (K := K) a b - μ • 1).rank ≤ 4 - 2 :=
  l5_t3_corrected A μ a b hab (by omega) hsmall

example (hμ : μ ≠ 0) (hrank : (A - μ • 1).rank = 4 - 2)
    (hcol : transpositionVector (K := K) a b ∉
      LinearMap.range (A - μ • 1).mulVecLin)
    (hrow : transpositionVector (K := K) a b ∉
      LinearMap.range (A - μ • 1).transpose.mulVecLin) :
    (A * transpositionMatrix (K := K) a b - μ • 1).rank = 4 - 1 :=
  l6prime_t2_corrected A μ a b hab hμ (by omega) hrank hcol hrow

end FourByFourExamples

#print axioms l1_matrix_identity
#print axioms l1_mul_self
#print axioms l1_unit_inv
#print axioms l1_matrix_inv
#print axioms rank_mul_transposition
#print axioms smul_vecMulVec
#print axioms l2_rank_identity
#print axioms matrix_rank_add_le
#print axioms l3_rank_one_update_bounds
#print axioms l4_t0
#print axioms l5_t3_corrected
#print axioms exists_ker_dotProduct_ne_zero_of_not_mem_range_transpose
#print axioms l6a_rank_one_update_eq_add_one
#print axioms l6prime_t2_corrected
#print axioms one_mu_coefficients_eq_zero
#print axioms l7_quadratic_descent_with_decomposition

end K1695
