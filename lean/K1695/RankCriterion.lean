import K1695.StratumB

open scoped Matrix

namespace K1695

open Matrix Polynomial

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- The final degree bridge: once the matrix minimal polynomial has full
degree, divisibility and monicity identify it with the characteristic
polynomial. -/
theorem minpoly_eq_charpoly_of_natDegree_eq {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K)
    (hdeg : (minpoly K M).natDegree = n) :
    minpoly K M = M.charpoly := by
  apply Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff
    (Matrix.minpoly_dvd_charpoly M)
  · simp [hdeg]
  · rw [(minpoly.monic (Algebra.IsIntegral.isIntegral M)).leadingCoeff,
      (Matrix.charpoly_monic M).leadingCoeff]

/-- Every `2 × 2` minor of a matrix of rank at most one vanishes. -/
theorem det_submatrix_fin_two_eq_zero_of_rank_le_one {n : ℕ}
    (B : Matrix (Fin n) (Fin n) L) (r c : Fin 2 → Fin n)
    (hrank : B.rank ≤ 1) : (B.submatrix r c).det = 0 := by
  by_contra hdet
  have hfull : (B.submatrix r c).rank = 2 := by
    simpa using Matrix.rank_of_det_ne_zero hdet
  have hle := Matrix.rank_submatrix_le B r c
  omega

/-- A matrix defined over `F`, shifted by a genuinely quadratic scalar, cannot
have rank at most one once its size is at least three.  This is the finite
minor argument needed for the lower half of the stratum-(b) nullity lemma. -/
theorem rank_two_le_map_sub_quadratic_scalar
    (A : Matrix (Fin 4) (Fin 4) F) (μ : L)
    (hμbase : μ ∉ Set.range (algebraMap F L)) (s t : F)
    (hquad : μ * μ = algebraMap F L s + algebraMap F L t * μ) :
    2 ≤ (A.map (algebraMap F L) - μ • 1).rank := by
  let E := A.map (algebraMap F L) - μ • 1
  by_contra hnot
  change ¬ 2 ≤ E.rank at hnot
  have hrank : E.rank ≤ 1 := by omega
  have hminor (r c : Fin 2 → Fin 4) : (E.submatrix r c).det = 0 :=
    det_submatrix_fin_two_eq_zero_of_rank_le_one E r c hrank
  have h01 := hminor ![0, 1] ![0, 1]
  have h02 := hminor ![0, 2] ![0, 2]
  have h12 := hminor ![1, 2] ![1, 2]
  have hx := hminor ![0, 2] ![0, 1]
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, E, Matrix.sub_apply,
    Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at h01 h02 h12 hx
  norm_num at h01 h02 h12 hx
  have h02ne : (0 : Fin 4) ≠ 2 := by decide
  have h20ne : (2 : Fin 4) ≠ 0 := by decide
  have h12ne : (1 : Fin 4) ≠ 2 := by decide
  have h21ne : (2 : Fin 4) ≠ 1 := by decide
  simp only [h02ne, h20ne, h12ne, h21ne, ite_false, sub_zero] at h02 h12 hx
  have hsum (aii ajj aij aji : F)
      (h : (algebraMap F L aii - μ) * (algebraMap F L ajj - μ) -
        algebraMap F L aij * algebraMap F L aji = 0) :
      aii + ajj = t := by
    have hcoeff :
        algebraMap F L (aii * ajj - aij * aji + s) +
          μ * algebraMap F L (t - aii - ajj) = 0 := by
      simp only [map_add, map_sub, map_mul]
      linear_combination h - hquad
    have hc := (one_mu_coefficients_eq_zero μ hμbase
      (aii * ajj - aij * aji + s) (t - aii - ajj) hcoeff).2
    linear_combination -hc
  have hd01 : A 0 0 + A 1 1 = t := hsum _ _ _ _ h01
  have hd02 : A 0 0 + A 2 2 = t := hsum _ _ _ _ h02
  have hd12 : A 1 1 + A 2 2 = t := hsum _ _ _ _ h12
  have hd0eq1 : A 0 0 = A 1 1 := by linear_combination hd02 - hd12
  have hd1eq2 : A 1 1 = A 2 2 := by linear_combination hd01 - hd02
  have hμne : algebraMap F L (A 0 0) - μ ≠ 0 := by
    intro hzero
    apply hμbase
    exact ⟨A 0 0, sub_eq_zero.mp hzero⟩
  have hprod12 :
      algebraMap F L (A 1 2) * algebraMap F L (A 2 1) =
        (algebraMap F L (A 0 0) - μ) ^ 2 := by
    rw [hd0eq1, hd1eq2]
    rw [hd1eq2] at h12
    linear_combination -h12
  have ha21 : A 2 1 ≠ 0 := by
    intro ha21
    have hsquare : (algebraMap F L (A 0 0) - μ) ^ 2 = 0 := by
      rw [← hprod12, ha21]
      simp
    exact hμne (sq_eq_zero_iff.mp hsquare)
  apply hμbase
  refine ⟨A 0 0 - A 0 1 * A 2 0 / A 2 1, ?_⟩
  simp only [map_sub, map_div₀, map_mul]
  have hmap21 : algebraMap F L (A 2 1) ≠ 0 :=
    (map_ne_zero (algebraMap F L)).2 ha21
  field_simp [hmap21]
  linear_combination hx

/-- Scalar extension preserves the displayed quadratic annihilator. -/
theorem map_quadratic_annihilator {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (s t : F)
    (hzero : A * A - t • A - s • 1 = 0) :
    A.map (algebraMap F L) * A.map (algebraMap F L) -
        algebraMap F L t • A.map (algebraMap F L) -
        algebraMap F L s • 1 = 0 := by
  ext i j
  have hij := congrArg (algebraMap F L) (congrFun (congrFun hzero i) j)
  by_cases heq : i = j
  · subst j
    simpa [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.algebraMap_matrix_apply, Algebra.smul_def, map_sum] using hij
  · simpa [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.algebraMap_matrix_apply, Algebra.smul_def, map_sum, heq] using hij

/-- Product formula for the two shifts paired by a quadratic annihilator. -/
theorem quadratic_shift_mul_conjugate_shift {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (μ : L) (s t : F)
    (hzero : A * A - t • A - s • 1 = 0) :
    (A.map (algebraMap F L) - μ • 1) *
      (A.map (algebraMap F L) - (algebraMap F L t - μ) • 1) =
        (algebraMap F L s + algebraMap F L t * μ - μ * μ) • 1 := by
  let B := A.map (algebraMap F L)
  have hzeroL := map_quadratic_annihilator (L := L) A s t hzero
  change (B - μ • 1) * (B - (algebraMap F L t - μ) • 1) =
    (algebraMap F L s + algebraMap F L t * μ - μ * μ) • 1
  change B * B - algebraMap F L t • B - algebraMap F L s • 1 = 0 at hzeroL
  have hBB : B * B = algebraMap F L t • B + algebraMap F L s • 1 := by
    have h1 := sub_eq_zero.mp hzeroL
    have h2 := (sub_eq_iff_eq_add).mp h1
    simpa [add_comm] using h2
  rw [sub_mul, mul_sub]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]
  rw [hBB]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs
  · ring
  · ring

/-- The two conjugate shifts multiply to zero at a root of the quadratic. -/
theorem quadratic_conjugate_shift_mul_eq_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (μ : L) (s t : F)
    (hquad : μ * μ = algebraMap F L s + algebraMap F L t * μ)
    (hzero : A * A - t • A - s • 1 = 0) :
    (A.map (algebraMap F L) - μ • 1) *
      (A.map (algebraMap F L) - (algebraMap F L t - μ) • 1) = 0 := by
  rw [quadratic_shift_mul_conjugate_shift A μ s t hzero]
  have hc : algebraMap F L s + algebraMap F L t * μ - μ * μ = 0 := by
    linear_combination -hquad
  rw [hc, zero_smul]

/-- Away from the roots of its quadratic annihilator, the shifted matrix has
full rank. -/
theorem quadratic_nonroot_shift_rank_eq_four
    (A : Matrix (Fin 4) (Fin 4) F) (μ : L) (s t : F)
    (hnroot : μ * μ ≠ algebraMap F L s + algebraMap F L t * μ)
    (hzero : A * A - t • A - s • 1 = 0) :
    (A.map (algebraMap F L) - μ • 1).rank = 4 := by
  let c : L := algebraMap F L s + algebraMap F L t * μ - μ * μ
  have hc : c ≠ 0 := by
    intro hc0
    apply hnroot
    dsimp only [c] at hc0
    linear_combination -hc0
  have hprod := quadratic_shift_mul_conjugate_shift A μ s t hzero
  have hscalar : (c • (1 : Matrix (Fin 4) (Fin 4) L)).rank = 4 := by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero hc), Matrix.rank_one, Fintype.card_fin]
  have hle := Matrix.rank_mul_le_left
    (A.map (algebraMap F L) - μ • 1)
    (A.map (algebraMap F L) - (algebraMap F L t - μ) • 1)
  change _ = c • 1 at hprod
  rw [hprod, hscalar] at hle
  exact le_antisymm (Matrix.rank_le_width _) hle

/-- The T0 transposition bound away from the roots of a quadratic
annihilator. -/
theorem quadratic_nonroot_transposition_rank_ge_three
    (A : Matrix (Fin 4) (Fin 4) F) (μ : L) (s t : F)
    (hnroot : μ * μ ≠ algebraMap F L s + algebraMap F L t * μ)
    (hzero : A * A - t • A - s • 1 = 0)
    (a b : Fin 4) (hab : a ≠ b) :
    3 ≤ (A.map (algebraMap F L) * Matrix.swap L a b - μ • 1).rank := by
  have hfull := quadratic_nonroot_shift_rank_eq_four A μ s t hnroot hzero
  change 3 ≤ (A.map (algebraMap F L) *
    transpositionMatrix (K := L) a b - μ • 1).rank
  simpa using l4_t0 (A.map (algebraMap F L)) μ a b hab hfull

/-- The root shift has exact rank two for a four-dimensional matrix annihilated
by a quadratic, provided the root is not in the base field.  The proof treats
separable and inseparable quadratics uniformly. -/
theorem quadratic_root_shift_rank_eq_two
    (A : Matrix (Fin 4) (Fin 4) F) (μ : L)
    (hμbase : μ ∉ Set.range (algebraMap F L)) (s t : F)
    (hquad : μ * μ = algebraMap F L s + algebraMap F L t * μ)
    (hzero : A * A - t • A - s • 1 = 0) :
    (A.map (algebraMap F L) - μ • 1).rank = 2 := by
  let ν : L := algebraMap F L t - μ
  have hνbase : ν ∉ Set.range (algebraMap F L) := by
    rintro ⟨c, hc⟩
    apply hμbase
    refine ⟨t - c, ?_⟩
    simp only [map_sub]
    change algebraMap F L c = ν at hc
    dsimp only [ν] at hc
    linear_combination -hc
  have hνquad : ν * ν = algebraMap F L s + algebraMap F L t * ν := by
    dsimp only [ν]
    linear_combination hquad
  have hμlo : 2 ≤ (A.map (algebraMap F L) - μ • 1).rank :=
    rank_two_le_map_sub_quadratic_scalar A μ hμbase s t hquad
  have hνlo : 2 ≤ (A.map (algebraMap F L) - ν • 1).rank :=
    rank_two_le_map_sub_quadratic_scalar A ν hνbase s t hνquad
  have hprod : (A.map (algebraMap F L) - μ • 1) *
      (A.map (algebraMap F L) - ν • 1) = 0 := by
    simpa only [ν] using quadratic_conjugate_shift_mul_eq_zero A μ s t hquad hzero
  have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero hprod
  have hcard : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
  rw [hcard] at hsum
  omega

/-- Ticket-facing form of the stratum-(b) nullity lemma.  Irreducibility and
degree two force a root in an extension to lie outside the base field, so the
minor argument applies with no extra nullity or non-rationality hypothesis. -/
theorem stratumB_root_shift_rank_eq_two
    (A : Matrix (Fin 4) (Fin 4) F)
    (m : F[X]) (hm : Irreducible m) (hdeg : m.natDegree = 2)
    (hmin : minpoly F A = m) (μ : L)
    (hroot : Polynomial.IsRoot (m.map (algebraMap F L)) μ) :
    (A.map (algebraMap F L) - μ • 1).rank = 2 := by
  have hμbase : μ ∉ Set.range (algebraMap F L) := by
    rintro ⟨c, rfl⟩
    have hnotroot : ¬m.IsRoot c := hm.not_isRoot_of_natDegree_ne_one (by omega)
    apply hnotroot
    rw [Polynomial.IsRoot, Polynomial.eval_map] at hroot
    rw [Polynomial.IsRoot]
    apply FaithfulSMul.algebraMap_injective F L
    simpa using hroot
  have hmonic : m.Monic := by
    rw [← hmin]
    exact minpoly.monic (Algebra.IsIntegral.isIntegral A)
  let s : F := -m.coeff 0
  let t : F := -m.coeff 1
  have hmform : m =
      Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X - Polynomial.C s := by
    simpa only [s, t] using monic_quadratic_normal_form m hmonic hdeg
  have hquad : μ * μ = algebraMap F L s + algebraMap F L t * μ := by
    simpa only [s, t] using quadratic_relation_of_root m hmonic hdeg μ hroot
  have hzero : A * A - t • A - s • 1 = 0 :=
    quadratic_annihilator_of_minpoly A s t (hmin.trans hmform)
  exact quadratic_root_shift_rank_eq_two A μ hμbase s t hquad hzero

/-- K6-LEAN6's exact root-rank theorem with its former nullity hypothesis now
discharged by `stratumB_root_shift_rank_eq_two`. -/
theorem stratumB_rank_at_root_of_simple_extension
    (A : Matrix (Fin 4) (Fin 4) F) (hA : IsUnit A.det)
    (m : F[X]) (hm : Irreducible m) (hdeg : m.natDegree = 2)
    (hmin : minpoly F A = m)
    (μ : L) (hμint : IsIntegral F μ)
    (hadjoin : Algebra.adjoin F ({μ} : Set L) = ⊤)
    (hμdeg : (minpoly F μ).natDegree = 2)
    (hroot : Polynomial.IsRoot (m.map (algebraMap F L)) μ)
    (a b : Fin 4) (hab : a ≠ b) :
    (A.map (algebraMap F L) * Matrix.swap L a b - μ • 1).rank = 3 := by
  have hnull := stratumB_root_shift_rank_eq_two A m hm hdeg hmin μ hroot
  exact stratumB_rank_at_root_of_simple_extension_and_nullity
    A hA m hm hdeg hmin μ hμint hadjoin hμdeg hroot hnull a b hab

#print axioms minpoly_eq_charpoly_of_natDegree_eq
#print axioms det_submatrix_fin_two_eq_zero_of_rank_le_one
#print axioms rank_two_le_map_sub_quadratic_scalar
#print axioms map_quadratic_annihilator
#print axioms quadratic_shift_mul_conjugate_shift
#print axioms quadratic_conjugate_shift_mul_eq_zero
#print axioms quadratic_nonroot_shift_rank_eq_four
#print axioms quadratic_nonroot_transposition_rank_ge_three
#print axioms quadratic_root_shift_rank_eq_two
#print axioms stratumB_root_shift_rank_eq_two
#print axioms stratumB_rank_at_root_of_simple_extension

end K1695
