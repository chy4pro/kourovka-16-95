import K1695.TranspositionLemma

open scoped Matrix

namespace K1695

open Matrix

variable {K : Type*} [Field K]
variable {n : ℕ}

/-- A row-space vector annihilates the kernel. -/
theorem dotProduct_eq_zero_of_mem_range_transpose_of_mulVec_eq_zero
    (E : Matrix (Fin n) (Fin n) K) (y k : Fin n → K)
    (hy : y ∈ LinearMap.range E.transpose.mulVecLin)
    (hk : E *ᵥ k = 0) :
    y ⬝ᵥ k = 0 := by
  obtain ⟨u, rfl⟩ := hy
  rw [Matrix.mulVecLin_apply]
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec, hk]
  exact dotProduct_zero _

/-- The scalar attached to a preimage of `x` is independent of the chosen
preimage when `y` belongs to the row space. -/
theorem dotProduct_preimage_well_defined
    (E : Matrix (Fin n) (Fin n) K) (x y z z' : Fin n → K)
    (hy : y ∈ LinearMap.range E.transpose.mulVecLin)
    (hz : E *ᵥ z = x) (hz' : E *ᵥ z' = x) :
    y ⬝ᵥ z = y ⬝ᵥ z' := by
  have hker : E *ᵥ (z - z') = 0 := by
    rw [Matrix.mulVec_sub, hz, hz', sub_self]
  have hzero :=
    dotProduct_eq_zero_of_mem_range_transpose_of_mulVec_eq_zero E y (z - z') hy hker
  exact sub_eq_zero.mp (by simpa [dotProduct_sub] using hzero)

/-- If the first vector of a rank-one update is in the column space, the
updated image remains in that column space. -/
theorem rank_one_update_le_of_left_mem
    (E : Matrix (Fin n) (Fin n) K) (x y : Fin n → K)
    (hx : x ∈ LinearMap.range E.mulVecLin) :
    (E + Matrix.vecMulVec x y).rank ≤ E.rank := by
  obtain ⟨u, hu⟩ := hx
  have hu' : E *ᵥ u = x := by
    simpa only [Matrix.mulVecLin_apply] using hu
  rw [Matrix.rank, Matrix.rank]
  apply Submodule.finrank_mono
  rintro _ ⟨v, rfl⟩
  refine ⟨v + (y ⬝ᵥ v) • u, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec,
    Matrix.vecMulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    op_smul_eq_smul, hu']

/-- The transpose version of `rank_one_update_le_of_left_mem`. -/
theorem rank_one_update_le_of_right_mem
    (E : Matrix (Fin n) (Fin n) K) (x y : Fin n → K)
    (hy : y ∈ LinearMap.range E.transpose.mulVecLin) :
    (E + Matrix.vecMulVec x y).rank ≤ E.rank := by
  calc
    (E + Matrix.vecMulVec x y).rank =
        (E + Matrix.vecMulVec x y).transpose.rank :=
      (Matrix.rank_transpose _).symm
    _ = (E.transpose + Matrix.vecMulVec y x).rank := by
      rw [Matrix.transpose_add, Matrix.transpose_vecMulVec]
    _ ≤ E.transpose.rank := rank_one_update_le_of_left_mem E.transpose y x hy
    _ = E.rank := Matrix.rank_transpose E

/-- M2: if either update vector lies on the corresponding side of the
range, a rank-one update cannot increase rank. -/
theorem rank_one_update_le_of_one_side_mem
    (E : Matrix (Fin n) (Fin n) K) (x y : Fin n → K)
    (h : x ∈ LinearMap.range E.mulVecLin ∨
      y ∈ LinearMap.range E.transpose.mulVecLin) :
    (E + Matrix.vecMulVec x y).rank ≤ E.rank := by
  rcases h with hx | hy
  · exact rank_one_update_le_of_left_mem E x y hx
  · exact rank_one_update_le_of_right_mem E x y hy

/-- If exactly the column-side vector is transverse, while the row-side
vector lies in the row space, the rank is unchanged. -/
theorem rank_one_update_eq_of_left_not_mem_right_mem
    (E : Matrix (Fin n) (Fin n) K) (x y : Fin n → K)
    (hx : x ∉ LinearMap.range E.mulVecLin)
    (hy : y ∈ LinearMap.range E.transpose.mulVecLin) :
    (E + Matrix.vecMulVec x y).rank = E.rank := by
  let U := E + Matrix.vecMulVec x y
  have hker : LinearMap.ker U.mulVecLin = LinearMap.ker E.mulVecLin := by
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have huv : E *ᵥ v + (y ⬝ᵥ v) • x = 0 := by
        simpa [U, Matrix.add_mulVec, Matrix.vecMulVec_mulVec] using hv
      by_contra hev
      have hc : y ⬝ᵥ v ≠ 0 := by
        intro hc
        rw [hc, zero_smul, add_zero] at huv
        exact hev huv
      apply hx
      refine ⟨(-(y ⬝ᵥ v))⁻¹ • v, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul]
      have he : E *ᵥ v = -(y ⬝ᵥ v) • x := by
        simpa only [neg_smul] using eq_neg_of_add_eq_zero_left huv
      rw [he, smul_smul]
      simp [hc]
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have hdot :=
        dotProduct_eq_zero_of_mem_range_transpose_of_mulVec_eq_zero E y v hy hv
      simp [U, Matrix.vecMulVec_mulVec, hv, hdot]
  have hnullE := E.mulVecLin.finrank_range_add_finrank_ker
  have hnullU := U.mulVecLin.finrank_range_add_finrank_ker
  rw [hker] at hnullU
  simpa only [Matrix.rank, U] using Nat.add_right_cancel (hnullU.trans hnullE.symm)

/-- The symmetric unchanged-rank case. -/
theorem rank_one_update_eq_of_left_mem_right_not_mem
    (E : Matrix (Fin n) (Fin n) K) (x y : Fin n → K)
    (hx : x ∈ LinearMap.range E.mulVecLin)
    (hy : y ∉ LinearMap.range E.transpose.mulVecLin) :
    (E + Matrix.vecMulVec x y).rank = E.rank := by
  calc
    (E + Matrix.vecMulVec x y).rank =
        (E + Matrix.vecMulVec x y).transpose.rank :=
      (Matrix.rank_transpose _).symm
    _ = (E.transpose + Matrix.vecMulVec y x).rank := by
      rw [Matrix.transpose_add, Matrix.transpose_vecMulVec]
    _ = E.transpose.rank :=
      rank_one_update_eq_of_left_not_mem_right_mem E.transpose y x hy hx
    _ = E.rank := Matrix.rank_transpose E

/-- M1, drop case: the scalar equation adds exactly one kernel dimension. -/
theorem rank_one_update_eq_sub_one
    (E : Matrix (Fin n) (Fin n) K) (x y z : Fin n → K)
    (_hx : x ∈ LinearMap.range E.mulVecLin)
    (hy : y ∈ LinearMap.range E.transpose.mulVecLin)
    (hz : E *ᵥ z = x) (hdrop : 1 + y ⬝ᵥ z = 0) :
    (E + Matrix.vecMulVec x y).rank = E.rank - 1 := by
  let U := E + Matrix.vecMulVec x y
  have hx0 : x ≠ 0 := by
    intro hx0
    have hz0 : y ⬝ᵥ z = 0 :=
      dotProduct_eq_zero_of_mem_range_transpose_of_mulVec_eq_zero E y z hy (hz.trans hx0)
    rw [hz0, add_zero] at hdrop
    exact one_ne_zero hdrop
  have hker_le : LinearMap.ker E.mulVecLin ≤ LinearMap.ker U.mulVecLin := by
    intro k hk
    rw [LinearMap.mem_ker] at hk ⊢
    have hdot :=
      dotProduct_eq_zero_of_mem_range_transpose_of_mulVec_eq_zero E y k hy hk
    simp [U, Matrix.vecMulVec_mulVec, hk, hdot]
  have hzU : z ∈ LinearMap.ker U.mulVecLin := by
    rw [LinearMap.mem_ker]
    simp only [U, Matrix.mulVecLin_apply, Matrix.add_mulVec,
      Matrix.vecMulVec_mulVec, hz, op_smul_eq_smul]
    simpa only [add_smul, one_smul, zero_smul] using
      congrArg (fun c : K => c • x) hdrop
  have hzE : z ∉ LinearMap.ker E.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hz]
    exact hx0
  have hker_lt : LinearMap.ker E.mulVecLin < LinearMap.ker U.mulVecLin := by
    exact lt_of_le_of_ne hker_le (fun heq => hzE (heq ▸ hzU))
  have hfinrank_lt := Submodule.finrank_lt_finrank_of_lt hker_lt
  have hnullE := E.mulVecLin.finrank_range_add_finrank_ker
  have hnullU := U.mulVecLin.finrank_range_add_finrank_ker
  have hnullE' : E.rank + Module.finrank K (LinearMap.ker E.mulVecLin) =
      Module.finrank K (Fin n → K) := by
    simpa only [Matrix.rank] using hnullE
  have hnullU' : U.rank + Module.finrank K (LinearMap.ker U.mulVecLin) =
      Module.finrank K (Fin n → K) := by
    simpa only [Matrix.rank] using hnullU
  have hrank_lt : U.rank < E.rank := by
    omega
  have hlower := (l3_rank_one_update_bounds E x y).1
  change E.rank - 1 ≤ U.rank at hlower
  change U.rank = E.rank - 1
  exact le_antisymm (Nat.le_sub_one_of_lt hrank_lt) hlower

/-- M1, non-drop case: once both vectors lie in their corresponding ranges,
the complementary scalar condition makes the update rank-neutral. -/
theorem rank_one_update_eq_of_preimage_scalar_ne_zero
    (E : Matrix (Fin n) (Fin n) K) (x y z : Fin n → K)
    (_hx : x ∈ LinearMap.range E.mulVecLin)
    (hy : y ∈ LinearMap.range E.transpose.mulVecLin)
    (hz : E *ᵥ z = x) (hnodrop : 1 + y ⬝ᵥ z ≠ 0) :
    (E + Matrix.vecMulVec x y).rank = E.rank := by
  let U := E + Matrix.vecMulVec x y
  have hker : LinearMap.ker U.mulVecLin = LinearMap.ker E.mulVecLin := by
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      let c := y ⬝ᵥ v
      have huv : E *ᵥ v + c • x = 0 := by
        simpa [U, c, Matrix.add_mulVec, Matrix.vecMulVec_mulVec] using hv
      have hk : E *ᵥ (v + c • z) = 0 := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, hz]
        exact huv
      have hdotk :=
        dotProduct_eq_zero_of_mem_range_transpose_of_mulVec_eq_zero
          E y (v + c • z) hy hk
      have hc : c = 0 := by
        have : c * (1 + y ⬝ᵥ z) = 0 := by
          simpa [c, dotProduct_add, dotProduct_smul, mul_add, mul_comm,
            mul_left_comm, mul_assoc] using hdotk
        exact (mul_eq_zero.mp this).resolve_right hnodrop
      rw [hc, zero_smul, add_zero] at huv
      exact huv
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have hdot :=
        dotProduct_eq_zero_of_mem_range_transpose_of_mulVec_eq_zero E y v hy hv
      simp [U, Matrix.vecMulVec_mulVec, hv, hdot]
  have hnullE := E.mulVecLin.finrank_range_add_finrank_ker
  have hnullU := U.mulVecLin.finrank_range_add_finrank_ker
  rw [hker] at hnullU
  simpa only [Matrix.rank, U] using Nat.add_right_cancel (hnullU.trans hnullE.symm)

/-- T2, the direction complementary to `l6prime_t2_corrected`: membership
on either side prevents the transposition update from increasing rank. -/
theorem t2_rank_le_of_one_side_mem
    (A : Matrix (Fin n) (Fin n) K) (μ : K)
    (a b : Fin n) (hab : a ≠ b)
    (hrank : (A - μ • 1).rank = n - 2)
    (hside : transpositionVector (K := K) a b ∈
        LinearMap.range (A - μ • 1).mulVecLin ∨
      transpositionVector (K := K) a b ∈
        LinearMap.range (A - μ • 1).transpose.mulVecLin) :
    (A * transpositionMatrix (K := K) a b - μ • 1).rank ≤ n - 2 := by
  let E := A - μ • 1
  let d := transpositionVector (K := K) a b
  have hside' : μ • d ∈ LinearMap.range E.mulVecLin ∨
      d ∈ LinearMap.range E.transpose.mulVecLin := by
    rcases hside with hcol | hrow
    · left
      exact (LinearMap.range E.mulVecLin).smul_mem μ (by simpa only [E, d] using hcol)
    · exact Or.inr (by simpa only [E, d] using hrow)
  have hle := rank_one_update_le_of_one_side_mem E (μ • d) d hside'
  rw [← smul_vecMulVec] at hle
  rw [l2_rank_identity A μ a b hab]
  change (E + μ • Matrix.vecMulVec d d).rank ≤ n - 2
  exact hle.trans_eq (by simpa only [E] using hrank)

/-- Full T2: in the rank `n-2` case the update has rank `n-1` exactly
when the transposition vector is transverse to both column and row spaces. -/
theorem t2_rank_eq_iff_both_sides_not_mem
    (A : Matrix (Fin n) (Fin n) K) (μ : K)
    (a b : Fin n) (hab : a ≠ b) (hμ : μ ≠ 0)
    (hrank : (A - μ • 1).rank = n - 2) :
    (A * transpositionMatrix (K := K) a b - μ • 1).rank = n - 1 ↔
      transpositionVector (K := K) a b ∉
          LinearMap.range (A - μ • 1).mulVecLin ∧
        transpositionVector (K := K) a b ∉
          LinearMap.range (A - μ • 1).transpose.mulVecLin := by
  have hn : 2 ≤ n := by
    omega
  constructor
  · intro hup
    constructor
    · intro hcol
      have hle := t2_rank_le_of_one_side_mem A μ a b hab hrank (Or.inl hcol)
      omega
    · intro hrow
      have hle := t2_rank_le_of_one_side_mem A μ a b hab hrank (Or.inr hrow)
      omega
  · rintro ⟨hcol, hrow⟩
    exact l6prime_t2_corrected A μ a b hab hμ hn hrank hcol hrow

/-- T1 in both directions.  At rank `n-1`, dropping to `n-2` is exactly
the two-sided range condition together with the exceptional preimage scalar. -/
theorem t1_rank_drop_iff
    (A : Matrix (Fin n) (Fin n) K) (μ : K)
    (a b : Fin n) (hab : a ≠ b) (_hμ : μ ≠ 0)
    (hrank : (A - μ • 1).rank = n - 1) :
    (A * transpositionMatrix (K := K) a b - μ • 1).rank = n - 2 ↔
      transpositionVector (K := K) a b ∈
          LinearMap.range (A - μ • 1).transpose.mulVecLin ∧
        μ • transpositionVector (K := K) a b ∈
          LinearMap.range (A - μ • 1).mulVecLin ∧
        ∃ z, (A - μ • 1) *ᵥ z =
            μ • transpositionVector (K := K) a b ∧
          1 + transpositionVector (K := K) a b ⬝ᵥ z = 0 := by
  let E := A - μ • 1
  let d := transpositionVector (K := K) a b
  have hn : 2 ≤ n := by
    omega
  have hrankE : E.rank = n - 1 := by
    simpa only [E] using hrank
  have hrank_update :
      (A * transpositionMatrix (K := K) a b - μ • 1).rank =
        (E + Matrix.vecMulVec (μ • d) d).rank := by
    rw [l2_rank_identity A μ a b hab, smul_vecMulVec]
  constructor
  · intro hdrop_rank
    have hU : (E + Matrix.vecMulVec (μ • d) d).rank = n - 2 := by
      rwa [← hrank_update]
    have hne : (E + Matrix.vecMulVec (μ • d) d).rank ≠ E.rank := by
      rw [hU, hrankE]
      omega
    have hx : μ • d ∈ LinearMap.range E.mulVecLin := by
      by_contra hx
      by_cases hy : d ∈ LinearMap.range E.transpose.mulVecLin
      · exact hne (rank_one_update_eq_of_left_not_mem_right_mem E (μ • d) d hx hy)
      · have hi := l6a_rank_one_update_eq_add_one E (μ • d) d hx hy
        rw [hU, hrankE] at hi
        omega
    have hy : d ∈ LinearMap.range E.transpose.mulVecLin := by
      by_contra hy
      exact hne (rank_one_update_eq_of_left_mem_right_not_mem E (μ • d) d hx hy)
    have hxmem := hx
    obtain ⟨z, hz⟩ := hx
    have hz' : E *ᵥ z = μ • d := by
      simpa only [Matrix.mulVecLin_apply] using hz
    have hscalar : 1 + d ⬝ᵥ z = 0 := by
      by_contra hs
      exact hne (rank_one_update_eq_of_preimage_scalar_ne_zero
        E (μ • d) d z hxmem hy hz' hs)
    exact ⟨by simpa only [E, d] using hy,
      by simpa only [E, d] using hxmem,
      z, by simpa only [E, d] using hz', by simpa only [d] using hscalar⟩
  · rintro ⟨hy, hx, z, hz, hscalar⟩
    have hM1 := rank_one_update_eq_sub_one E (μ • d) d z
      (by simpa only [E, d] using hx) (by simpa only [E, d] using hy)
      (by simpa only [E, d] using hz) (by simpa only [d] using hscalar)
    rw [hrankE] at hM1
    have hU : (E + Matrix.vecMulVec (μ • d) d).rank = n - 2 := by
      omega
    rwa [hrank_update]

/-- T4, easy inclusion in general degree: evaluating the minimal polynomial
at `A` lands in the column space of `A - μ`. -/
theorem t4_minpoly_mulVec_mem_range
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (A : Matrix (Fin n) (Fin n) F) (μ : L)
    (_hμ : IsIntegral F μ) (z₁ : Fin n → F) :
    (fun i => algebraMap F L
      (((Polynomial.aeval A (minpoly F μ)).mulVec z₁) i)) ∈
      LinearMap.range (A.map (algebraMap F L) - μ • 1).mulVecLin := by
  classical
  let M := A.map (algebraMap F L)
  let q := Polynomial.aeval M (minpolyDiv F μ)
  let incl : (Fin n → F) → (Fin n → L) :=
    fun v i => algebraMap F L (v i)
  refine ⟨q *ᵥ incl z₁, ?_⟩
  change (M - μ • 1) *ᵥ (q *ᵥ incl z₁) = _
  rw [Matrix.mulVec_mulVec (incl z₁) (M - μ • 1) q]
  have hspec := congrArg (Polynomial.aeval M) (minpolyDiv_spec F μ)
  simp only [map_mul, Polynomial.aeval_sub, Polynomial.aeval_X,
    Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] at hspec
  have hcomm : Commute (M - μ • 1) q := by
    change Commute (M - μ • 1)
      (Polynomial.aeval M (minpolyDiv F μ))
    have heval : Polynomial.aeval M
        (Polynomial.X - Polynomial.C μ) = M - μ • 1 := by
      simp only [Polynomial.aeval_sub, Polynomial.aeval_X,
        Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    rw [← heval]
    exact (Commute.all (Polynomial.X - Polynomial.C μ)
      (minpolyDiv F μ)).map (Polynomial.aeval M)
  rw [hcomm.eq, hspec]
  have hmap : Polynomial.aeval M
      ((minpoly F μ).map (algebraMap F L)) =
      (Polynomial.aeval A (minpoly F μ)).map (algebraMap F L) := by
    symm
    exact Polynomial.map_aeval_eq_aeval_map
      (R := F) (S := Matrix (Fin n) (Fin n) F) (T := L)
      (U := Matrix (Fin n) (Fin n) L) (φ := algebraMap F L)
      (ψ := RingHom.mapMatrix (m := Fin n) (algebraMap F L)) (by
        ext x i j
        by_cases hij : i = j <;>
          simp [Algebra.algebraMap_eq_smul_one, hij]) (minpoly F μ) A
  rw [hmap]
  ext i
  simp [incl, Matrix.mulVec, dotProduct, map_sum]

/-- When the minimal polynomial has degree three, `1, μ, μ²` have unique
coefficients over the base field. -/
theorem cubic_coefficients_eq_zero
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (μ : L) (hdeg : (minpoly F μ).natDegree = 3)
    (c₀ c₁ c₂ : F)
    (h : algebraMap F L c₀ + μ * algebraMap F L c₁ +
      μ ^ 2 * algebraMap F L c₂ = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := by
  have hli := linearIndependent_pow (K := F) μ
  rw [hdeg] at hli
  let g : Fin 3 → F := ![c₀, c₁, c₂]
  have hsum : ∑ i : Fin 3, g i • μ ^ (i : ℕ) = 0 := by
    simp [g, Fin.sum_univ_three, Algebra.smul_def]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hg := Fintype.linearIndependent_iff.mp hli g hsum
  exact ⟨by simpa [g] using hg 0, by simpa [g] using hg 1,
    by simpa [g] using hg 2⟩

/-- T4 hard inclusion in the permitted cubic fallback, with the coordinate
decomposition made explicit. -/
theorem t4_cubic_descent_with_decomposition
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (A : Matrix (Fin n) (Fin n) F) (μ : L)
    (hdeg : (minpoly F μ).natDegree = 3)
    (s t u : F)
    (hcubic : μ ^ 3 = algebraMap F L s + μ * algebraMap F L t +
      μ ^ 2 * algebraMap F L u)
    (w z₀ z₁ z₂ : Fin n → F) (z : Fin n → L)
    (hz : z = fun i => algebraMap F L (z₀ i) +
      μ * algebraMap F L (z₁ i) + μ ^ 2 * algebraMap F L (z₂ i))
    (heq : (A.map (algebraMap F L) - μ • 1).mulVec z =
      fun i => algebraMap F L (w i)) :
    ∃ v : Fin n → F,
      w = (A ^ 3 - u • A ^ 2 - t • A - s • 1).mulVec v := by
  classical
  let incl : (Fin n → F) → (Fin n → L) :=
    fun v i => algebraMap F L (v i)
  have hmap_mulVec (v : Fin n → F) :
      (A.map (algebraMap F L)).mulVec (incl v) =
        incl (A.mulVec v) := by
    ext i
    simp [incl, Matrix.mulVec, dotProduct, map_sum]
  have hz' : z = incl z₀ + μ • incl z₁ + μ ^ 2 • incl z₂ := by
    rw [hz]
    ext i
    simp [incl]
  have hexpand :
      (A.map (algebraMap F L) - μ • 1).mulVec z = fun i =>
        algebraMap F L ((A.mulVec z₀ - s • z₂) i) +
          μ * algebraMap F L ((A.mulVec z₁ - z₀ - t • z₂) i) +
          μ ^ 2 * algebraMap F L
            ((A.mulVec z₂ - z₁ - u • z₂) i) := by
    rw [hz', Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.smul_mulVec,
      Matrix.one_mulVec, hmap_mulVec, hmap_mulVec, hmap_mulVec]
    ext i
    simp only [incl, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, RingHom.map_sub, RingHom.map_mul]
    linear_combination -(algebraMap F L (z₂ i)) * hcubic
  have hcoeff (i : Fin n) :
      algebraMap F L ((A.mulVec z₀ - s • z₂ - w) i) +
        μ * algebraMap F L ((A.mulVec z₁ - z₀ - t • z₂) i) +
        μ ^ 2 * algebraMap F L
          ((A.mulVec z₂ - z₁ - u • z₂) i) = 0 := by
    have hi := congrFun (hexpand.symm.trans heq) i
    simp only [Pi.sub_apply, Pi.smul_apply, RingHom.map_sub] at hi ⊢
    rw [← hi]
    ring
  have hbase : A.mulVec z₀ - s • z₂ - w = 0 := by
    ext i
    exact (cubic_coefficients_eq_zero μ hdeg _ _ _ (hcoeff i)).1
  have hlinear : A.mulVec z₁ - z₀ - t • z₂ = 0 := by
    ext i
    exact (cubic_coefficients_eq_zero μ hdeg _ _ _ (hcoeff i)).2.1
  have hquad : A.mulVec z₂ - z₁ - u • z₂ = 0 := by
    ext i
    exact (cubic_coefficients_eq_zero μ hdeg _ _ _ (hcoeff i)).2.2
  have hw : w = A.mulVec z₀ - s • z₂ :=
    (sub_eq_zero.mp hbase).symm
  have hz₁ : z₁ = A.mulVec z₂ - u • z₂ := by
    funext i
    have hi := congrFun hquad i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply] at hi ⊢
    linear_combination -hi
  have hz₀ : z₀ = A.mulVec z₁ - t • z₂ := by
    funext i
    have hi := congrFun hlinear i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply] at hi ⊢
    linear_combination -hi
  refine ⟨z₂, ?_⟩
  rw [hw, hz₀, hz₁]
  ext i
  simp [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.smul_mulVec, pow_succ,
    Matrix.mul_assoc]

/-- The cubic fallback stated with `aeval A (minpoly F μ)`. -/
theorem t4_cubic_minpoly_descent_with_decomposition
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (A : Matrix (Fin n) (Fin n) F) (μ : L)
    (hdeg : (minpoly F μ).natDegree = 3)
    (s t u : F)
    (hm : minpoly F μ =
      Polynomial.X ^ 3 - Polynomial.C u * Polynomial.X ^ 2 -
        Polynomial.C t * Polynomial.X - Polynomial.C s)
    (w z₀ z₁ z₂ : Fin n → F) (z : Fin n → L)
    (hz : z = fun i => algebraMap F L (z₀ i) +
      μ * algebraMap F L (z₁ i) + μ ^ 2 * algebraMap F L (z₂ i))
    (heq : (A.map (algebraMap F L) - μ • 1).mulVec z =
      fun i => algebraMap F L (w i)) :
    ∃ v : Fin n → F,
      w = (Polynomial.aeval A (minpoly F μ)).mulVec v := by
  have hroot := minpoly.aeval F μ
  rw [hm] at hroot
  simp only [map_sub, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C] at hroot
  have hcubic : μ ^ 3 = algebraMap F L s + μ * algebraMap F L t +
      μ ^ 2 * algebraMap F L u := by
    linear_combination hroot
  obtain ⟨v, hv⟩ := t4_cubic_descent_with_decomposition
    A μ hdeg s t u hcubic w z₀ z₁ z₂ z hz heq
  refine ⟨v, ?_⟩
  rw [hm]
  simp only [map_sub, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mul, Matrix.one_mul]
  exact hv

section FourByFourExamples

variable (A E : Matrix (Fin 4) (Fin 4) K) (μ : K)
variable (a b : Fin 4) (hab : a ≠ b)
variable (x y z : Fin 4 → K)

example (hx : x ∈ LinearMap.range E.mulVecLin)
    (hy : y ∈ LinearMap.range E.transpose.mulVecLin)
    (hz : E *ᵥ z = x) (hdrop : 1 + y ⬝ᵥ z = 0) :
    (E + Matrix.vecMulVec x y).rank = E.rank - 1 :=
  rank_one_update_eq_sub_one E x y z hx hy hz hdrop

example (hx : x ∈ LinearMap.range E.mulVecLin)
    (hy : y ∈ LinearMap.range E.transpose.mulVecLin)
    (hz : E *ᵥ z = x) (hnodrop : 1 + y ⬝ᵥ z ≠ 0) :
    (E + Matrix.vecMulVec x y).rank = E.rank :=
  rank_one_update_eq_of_preimage_scalar_ne_zero E x y z hx hy hz hnodrop

example (h : x ∈ LinearMap.range E.mulVecLin ∨
    y ∈ LinearMap.range E.transpose.mulVecLin) :
    (E + Matrix.vecMulVec x y).rank ≤ E.rank :=
  rank_one_update_le_of_one_side_mem E x y h

example (hrank : (A - μ • 1).rank = 4 - 2)
    (hside : transpositionVector (K := K) a b ∈
        LinearMap.range (A - μ • 1).mulVecLin ∨
      transpositionVector (K := K) a b ∈
        LinearMap.range (A - μ • 1).transpose.mulVecLin) :
    (A * transpositionMatrix (K := K) a b - μ • 1).rank ≤ 4 - 2 :=
  t2_rank_le_of_one_side_mem A μ a b hab hrank hside

example (hμ : μ ≠ 0) (hrank : (A - μ • 1).rank = 4 - 2) :
    (A * transpositionMatrix (K := K) a b - μ • 1).rank = 4 - 1 ↔
      transpositionVector (K := K) a b ∉
          LinearMap.range (A - μ • 1).mulVecLin ∧
        transpositionVector (K := K) a b ∉
          LinearMap.range (A - μ • 1).transpose.mulVecLin :=
  t2_rank_eq_iff_both_sides_not_mem A μ a b hab hμ hrank

example (hμ : μ ≠ 0) (hrank : (A - μ • 1).rank = 4 - 1) :
    (A * transpositionMatrix (K := K) a b - μ • 1).rank = 4 - 2 ↔
      transpositionVector (K := K) a b ∈
          LinearMap.range (A - μ • 1).transpose.mulVecLin ∧
        μ • transpositionVector (K := K) a b ∈
          LinearMap.range (A - μ • 1).mulVecLin ∧
        ∃ z, (A - μ • 1) *ᵥ z =
            μ • transpositionVector (K := K) a b ∧
          1 + transpositionVector (K := K) a b ⬝ᵥ z = 0 :=
  t1_rank_drop_iff A μ a b hab hμ hrank

example {F L : Type*} [Field F] [Field L] [Algebra F L]
    (B : Matrix (Fin 4) (Fin 4) F) (ν : L)
    (hν : IsIntegral F ν) (v : Fin 4 → F) :
    (fun i => algebraMap F L
      (((Polynomial.aeval B (minpoly F ν)).mulVec v) i)) ∈
      LinearMap.range (B.map (algebraMap F L) - ν • 1).mulVecLin :=
  t4_minpoly_mulVec_mem_range B ν hν v

example {F L : Type*} [Field F] [Field L] [Algebra F L]
    (B : Matrix (Fin 4) (Fin 4) F) (ν : L)
    (hdeg : (minpoly F ν).natDegree = 3) (s t u : F)
    (hm : minpoly F ν =
      Polynomial.X ^ 3 - Polynomial.C u * Polynomial.X ^ 2 -
        Polynomial.C t * Polynomial.X - Polynomial.C s)
    (w z₀ z₁ z₂ : Fin 4 → F) (zL : Fin 4 → L)
    (hz : zL = fun i => algebraMap F L (z₀ i) +
      ν * algebraMap F L (z₁ i) + ν ^ 2 * algebraMap F L (z₂ i))
    (heq : (B.map (algebraMap F L) - ν • 1).mulVec zL =
      fun i => algebraMap F L (w i)) :
    ∃ v : Fin 4 → F,
      w = (Polynomial.aeval B (minpoly F ν)).mulVec v :=
  t4_cubic_minpoly_descent_with_decomposition
    B ν hdeg s t u hm w z₀ z₁ z₂ zL hz heq

end FourByFourExamples

#print axioms dotProduct_eq_zero_of_mem_range_transpose_of_mulVec_eq_zero
#print axioms dotProduct_preimage_well_defined
#print axioms rank_one_update_le_of_left_mem
#print axioms rank_one_update_le_of_right_mem
#print axioms rank_one_update_le_of_one_side_mem
#print axioms rank_one_update_eq_of_left_not_mem_right_mem
#print axioms rank_one_update_eq_of_left_mem_right_not_mem
#print axioms rank_one_update_eq_sub_one
#print axioms rank_one_update_eq_of_preimage_scalar_ne_zero
#print axioms t2_rank_le_of_one_side_mem
#print axioms t2_rank_eq_iff_both_sides_not_mem
#print axioms t1_rank_drop_iff
#print axioms t4_minpoly_mulVec_mem_range
#print axioms cubic_coefficients_eq_zero
#print axioms t4_cubic_descent_with_decomposition
#print axioms t4_cubic_minpoly_descent_with_decomposition

end K1695
