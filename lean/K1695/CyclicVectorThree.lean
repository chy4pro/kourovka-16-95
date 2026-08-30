import Mathlib

open scoped Matrix

namespace K1695

open Matrix

variable {K : Type*} [Field K]

/-- The determinant of the matrix whose columns are `u` and `v`. -/
def detCols2 (u v : Fin 2 → K) : K :=
  u 0 * v 1 - u 1 * v 0

/-- The two-by-two matrix with first column `u` and second column `v`. -/
def matrixOfCols2 (u v : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => if j = 0 then u i else v i

/-- Controllability of a vector for a two-dimensional system. -/
def Ctrl2 (M : Matrix (Fin 2) (Fin 2) K) (b : Fin 2 → K) : Prop :=
  LinearIndependent K ![b, M *ᵥ b]

/-- Controllability/cyclicity of a vector for a three-dimensional system. -/
def Ctrl3 (M : Matrix (Fin 3) (Fin 3) K) (b : Fin 3 → K) : Prop :=
  LinearIndependent K ![b, M *ᵥ b, M *ᵥ (M *ᵥ b)]

/-- Delete coordinate zero from a three-vector. -/
def dropFirst (x : Fin 3 → K) : Fin 2 → K := fun r => x r.succ

/-- The bottom-right two-by-two block of a three-by-three matrix. -/
def lowerBlock (M : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  fun r s => M r.succ s.succ

/-- The three-by-three matrix with the indicated columns. -/
def matrixOfCols3 (x y z : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => if j = 0 then x i else if j = 1 then y i else z i

/-- Delete row zero from a three-by-three matrix. -/
def deleteFirstRow (A : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 2) (Fin 3) K := fun r j => A r.succ j

/-- Right multiplication by a permutation matrix permutes columns by the
inverse permutation. -/
theorem mul_permMatrix_apply (A : Matrix (Fin 3) (Fin 3) K)
    (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (A * σ.permMatrix K) i j = A i (σ.symm j) := by
  classical
  simp [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    ← Equiv.eq_symm_apply]

/-- Multiplication by a matrix presented by its two columns. -/
theorem matrixOfCols2_mulVec (u v b : Fin 2 → K) :
    matrixOfCols2 u v *ᵥ b = b 0 • u + b 1 • v := by
  ext i
  fin_cases i <;>
    simp [matrixOfCols2, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The determinant identity (*) from the ticket. -/
theorem detCols2_control_identity (b u v : Fin 2 → K) :
    detCols2 b (matrixOfCols2 u v *ᵥ b) =
      b 0 * detCols2 b u + b 1 * detCols2 b v := by
  rw [matrixOfCols2_mulVec]
  simp [detCols2]
  ring

/-- In dimension two, controllability is exactly nonvanishing of the
two-column determinant. -/
theorem ctrl2_iff_detCols2_ne_zero (M : Matrix (Fin 2) (Fin 2) K)
    (b : Fin 2 → K) :
    Ctrl2 M b ↔ detCols2 b (M *ᵥ b) ≠ 0 := by
  let C := matrixOfCols2 b (M *ᵥ b)
  have hcols : C.col = ![b, M *ᵥ b] := by
    funext j i
    fin_cases j <;> simp [C, matrixOfCols2]
  rw [Ctrl2, ← hcols, Matrix.linearIndependent_cols_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det]
  have hdet : C.det = detCols2 b (M *ᵥ b) := by
    simp [C, matrixOfCols2, detCols2, Matrix.det_fin_two]
    ring
  rw [hdet]
  exact isUnit_iff_ne_zero

/-- Two vectors in `K²` are independent exactly when their determinant is
nonzero. -/
theorem linearIndependent_pair_iff_detCols2_ne_zero (u v : Fin 2 → K) :
    LinearIndependent K ![u, v] ↔ detCols2 u v ≠ 0 := by
  let C := matrixOfCols2 u v
  have hcols : C.col = ![u, v] := by
    funext j i
    fin_cases j <;> simp [C, matrixOfCols2]
  rw [← hcols, Matrix.linearIndependent_cols_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det]
  have hdet : C.det = detCols2 u v := by
    simp [C, matrixOfCols2, detCols2, Matrix.det_fin_two]
    ring
  rw [hdet]
  exact isUnit_iff_ne_zero

/-- Expanding along the first standard basis vector reduces independence in
dimension three to the determinant of the last two coordinates. -/
theorem linearIndependent_e0_of_det_dropFirst_ne_zero (y z : Fin 3 → K)
    (h : detCols2 (dropFirst y) (dropFirst z) ≠ 0) :
    LinearIndependent K ![![1, 0, 0], y, z] := by
  let C := matrixOfCols3 ![1, 0, 0] y z
  have hcols : C.col = ![![1, 0, 0], y, z] := by
    funext j i
    fin_cases j <;> simp [C, matrixOfCols3]
  rw [← hcols, Matrix.linearIndependent_cols_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det]
  have hdet : C.det = detCols2 (dropFirst y) (dropFirst z) := by
    simp [C, matrixOfCols3, dropFirst, detCols2, Matrix.det_fin_three]
    ring
  rw [hdet]
  exact isUnit_iff_ne_zero.mpr h

/-- Feedback/deflation at coordinate zero: controllability of the lower block
implies cyclicity of the first standard basis vector. -/
theorem ctrl3_e0_of_ctrl2_lowerBlock (M : Matrix (Fin 3) (Fin 3) K)
    (hctrl : Ctrl2 (lowerBlock M) (dropFirst (M *ᵥ ![1, 0, 0]))) :
    Ctrl3 M ![1, 0, 0] := by
  let y : Fin 3 → K := M *ᵥ ![1, 0, 0]
  let z : Fin 3 → K := M *ᵥ y
  let b : Fin 2 → K := dropFirst y
  have hbdet : detCols2 b (lowerBlock M *ᵥ b) ≠ 0 := by
    exact (ctrl2_iff_detCols2_ne_zero (lowerBlock M) b).1 (by
      simpa only [b, y] using hctrl)
  have hz : dropFirst z = lowerBlock M *ᵥ b + M 0 0 • b := by
    ext r
    fin_cases r <;>
      simp [z, y, b, dropFirst, lowerBlock, Matrix.mulVec, dotProduct,
        Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have hzdet : detCols2 b (dropFirst z) ≠ 0 := by
    have heq : detCols2 b (dropFirst z) =
        detCols2 b (lowerBlock M *ᵥ b) := by
      rw [hz]
      simp [detCols2]
      ring
    rwa [heq]
  rw [Ctrl3]
  exact linearIndependent_e0_of_det_dropFirst_ne_zero y z hzdet

/-- Cyclic vectors are transported by matrix conjugation. -/
theorem ctrl3_conjugate (Q Qinv M : Matrix (Fin 3) (Fin 3) K)
    (v : Fin 3 → K) (hleft : Qinv * Q = 1)
    (hctrl : Ctrl3 M v) :
    Ctrl3 (Q * M * Qinv) (Q *ᵥ v) := by
  have hQinj : Function.Injective Q.mulVec := by
    intro x y hxy
    have h := congrArg (fun z => Qinv *ᵥ z) hxy
    simpa only [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] using h
  have hLI : LinearIndependent K
      (Q.mulVecLin ∘ ![v, M *ᵥ v, M *ᵥ (M *ᵥ v)]) := by
    exact hctrl.map' Q.mulVecLin (LinearMap.ker_eq_bot.mpr hQinj)
  have hconj (x : Fin 3 → K) :
      (Q * M * Qinv) *ᵥ (Q *ᵥ x) = Q *ᵥ (M *ᵥ x) := by
    calc
      (Q * M * Qinv) *ᵥ (Q *ᵥ x) = ((Q * M * Qinv) * Q) *ᵥ x :=
        Matrix.mulVec_mulVec _ _ _
      _ = (Q * M) *ᵥ x := by rw [Matrix.mul_assoc, hleft, Matrix.mul_one]
      _ = Q *ᵥ (M *ᵥ x) := (Matrix.mulVec_mulVec _ _ _).symm
  rw [Ctrl3, hconj v, hconj (M *ᵥ v)]
  convert hLI using 1
  funext i
  fin_cases i <;> rfl

/-- The permutation matrix of `(0 i)` sends the first standard basis vector
to the `i`-th one. -/
theorem swap_permMatrix_mulVec_e0 (i : Fin 3) :
    (Equiv.swap (0 : Fin 3) i).permMatrix K *ᵥ ![1, 0, 0] =
      Pi.single i 1 := by
  ext r
  fin_cases i <;> fin_cases r <;>
    simp [Matrix.permMatrix_mulVec, Equiv.swap_apply_def]

/-- An independent pair in `K²` spans every third vector, without choosing
coordinates by division. -/
theorem exists_pair_coordinates (u v w : Fin 2 → K)
    (huv : detCols2 u v ≠ 0) :
    ∃ α β : K, w = α • u + β • v := by
  have hli : LinearIndependent K ![u, v] :=
    (linearIndependent_pair_iff_detCols2_ne_zero u v).2 huv
  have hspan : Submodule.span K (Set.range ![u, v]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hwmem : w ∈ Submodule.span K (Set.range ![u, v]) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨q, hq⟩ :=
    (Submodule.mem_span_range_iff_exists_fun K).1 hwmem
  refine ⟨q 0, q 1, ?_⟩
  rw [← hq]
  simp only [Fin.sum_univ_two]
  change q 0 • u + q 1 • v = q 0 • u + q 1 • v
  rfl

/-- Division-free algebraic heart of T₂.  Here `(a,b)` and `(c,d)` are
independent columns and the third column is `α(a,b)+β(c,d)`. -/
theorem t2_six_choices_scalar (a b c d α β : K)
    (hD : a * d - b * c ≠ 0) :
    let D := a * d - b * c
    let e := α * a + β * c
    let f := α * b + β * d
    (a + β * b) * D ≠ 0 ∨
    (β * a + b) * D ≠ 0 ∨
    (-(c + α * d)) * D ≠ 0 ∨
    (-(α * c + d)) * D ≠ 0 ∨
    (-β * e + α * f) * D ≠ 0 ∨
    (α * e - β * f) * D ≠ 0 := by
  dsimp only
  by_contra h
  push Not at h
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  have e₁ : a + β * b = 0 := (mul_eq_zero.mp h₁).resolve_right hD
  have e₂ : β * a + b = 0 := (mul_eq_zero.mp h₂).resolve_right hD
  have e₃' : -(c + α * d) = 0 := (mul_eq_zero.mp h₃).resolve_right hD
  have e₄' : -(α * c + d) = 0 := (mul_eq_zero.mp h₄).resolve_right hD
  have e₃ : c + α * d = 0 := neg_eq_zero.mp e₃'
  have e₄ : α * c + d = 0 := neg_eq_zero.mp e₄'
  have e₅ : -β * (α * a + β * c) + α * (α * b + β * d) = 0 :=
    (mul_eq_zero.mp h₅).resolve_right hD
  have _e₆ : α * (α * a + β * c) - β * (α * b + β * d) = 0 :=
    (mul_eq_zero.mp h₆).resolve_right hD
  have hb : b ≠ 0 := by
    intro hb0
    have ha0 : a = 0 := by
      rw [hb0, mul_zero, add_zero] at e₁
      exact e₁
    apply hD
    rw [ha0, hb0]
    ring
  have hd : d ≠ 0 := by
    intro hd0
    have hc0 : c = 0 := by
      rw [hd0, mul_zero, add_zero] at e₃
      exact e₃
    apply hD
    rw [hc0, hd0]
    ring
  have ha : a = -β * b := by linear_combination e₁
  have hc : c = -α * d := by linear_combination e₃
  have hDform : a * d - b * c = (α - β) * b * d := by
    rw [ha, hc]
    ring
  have hαβ : α - β ≠ 0 := by
    intro hz
    apply hD
    rw [hDform, hz]
    ring
  have hβprod : (1 - β * β) * b = 0 := by
    linear_combination e₂ - β * e₁
  have hβsq : β * β = 1 := by
    have := (mul_eq_zero.mp hβprod).resolve_right hb
    linear_combination -this
  have hαprod : (1 - α * α) * d = 0 := by
    linear_combination e₄ - α * e₃
  have hαsq : α * α = 1 := by
    have := (mul_eq_zero.mp hαprod).resolve_right hd
    linear_combination -this
  have hpmprod : (α - β) * (α + β) = 0 := by
    linear_combination hαsq - hβsq
  have hsum : α + β = 0 :=
    (mul_eq_zero.mp hpmprod).resolve_left hαβ
  have hαcases : α = 1 ∨ α = -1 := by
    apply sq_eq_one_iff.mp
    simpa only [pow_two] using hαsq
  rcases hαcases with hα | hα
  · have hβ : β = -1 := by linear_combination hsum - hα
    have htwo : (2 : K) ≠ 0 := by
      intro hz
      apply hαβ
      rw [hα, hβ]
      linear_combination hz
    have htwo_b : (2 : K) * b = 0 := by
      simp only [hα, hβ] at e₁ e₃ e₅
      linear_combination e₅ - e₁ + e₃
    exact (mul_ne_zero htwo hb) htwo_b
  · have hβ : β = 1 := by linear_combination hsum - hα
    have htwo : (2 : K) ≠ 0 := by
      intro hz
      apply hαβ
      rw [hα, hβ]
      linear_combination -hz
    have htwo_d : (2 : K) * d = 0 := by
      simp only [hα, hβ] at e₁ e₃ e₅
      linear_combination -e₅ + e₁ - e₃
    exact (mul_ne_zero htwo hd) htwo_d

/-- T₂ with an indicated independent pair: among the six choices of a
distinguished vector and an ordering of the other two, one is controllable. -/
theorem t2_six_choices_of_first_pair (u v w : Fin 2 → K)
    (huv : detCols2 u v ≠ 0) :
    Ctrl2 (matrixOfCols2 v w) u ∨
    Ctrl2 (matrixOfCols2 w v) u ∨
    Ctrl2 (matrixOfCols2 u w) v ∨
    Ctrl2 (matrixOfCols2 w u) v ∨
    Ctrl2 (matrixOfCols2 u v) w ∨
    Ctrl2 (matrixOfCols2 v u) w := by
  obtain ⟨α, β, hw⟩ := exists_pair_coordinates u v w huv
  have h := t2_six_choices_scalar (u 0) (u 1) (v 0) (v 1) α β huv
  have q₁ : u 0 * detCols2 u v + u 1 * detCols2 u w =
      (u 0 + β * u 1) * (u 0 * v 1 - u 1 * v 0) := by
    rw [hw]
    simp [detCols2]
    ring
  have q₂ : u 0 * detCols2 u w + u 1 * detCols2 u v =
      (β * u 0 + u 1) * (u 0 * v 1 - u 1 * v 0) := by
    rw [hw]
    simp [detCols2]
    ring
  have q₃ : v 0 * detCols2 v u + v 1 * detCols2 v w =
      (-(v 0 + α * v 1)) * (u 0 * v 1 - u 1 * v 0) := by
    rw [hw]
    simp [detCols2]
    ring
  have q₄ : v 0 * detCols2 v w + v 1 * detCols2 v u =
      (-(α * v 0 + v 1)) * (u 0 * v 1 - u 1 * v 0) := by
    rw [hw]
    simp [detCols2]
    ring
  have q₅ : w 0 * detCols2 w u + w 1 * detCols2 w v =
      (-β * (α * u 0 + β * v 0) + α * (α * u 1 + β * v 1)) *
        (u 0 * v 1 - u 1 * v 0) := by
    rw [hw]
    simp [detCols2]
    ring
  have q₆ : w 0 * detCols2 w v + w 1 * detCols2 w u =
      (α * (α * u 0 + β * v 0) - β * (α * u 1 + β * v 1)) *
        (u 0 * v 1 - u 1 * v 0) := by
    rw [hw]
    simp [detCols2]
    ring
  simp_rw [ctrl2_iff_detCols2_ne_zero, detCols2_control_identity]
  rw [q₁, q₂, q₃, q₄, q₅, q₆]
  exact h

/-- The symmetric three-column form of T₂, assuming one of the three column
pairs has nonzero determinant. -/
theorem t2_three_columns_of_pair (c : Fin 3 → Fin 2 → K)
    (hpair : detCols2 (c 0) (c 1) ≠ 0 ∨
      detCols2 (c 0) (c 2) ≠ 0 ∨ detCols2 (c 1) (c 2) ≠ 0) :
    ∃ j k l : Fin 3, j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      Ctrl2 (matrixOfCols2 (c k) (c l)) (c j) := by
  have hall :
      Ctrl2 (matrixOfCols2 (c 1) (c 2)) (c 0) ∨
      Ctrl2 (matrixOfCols2 (c 2) (c 1)) (c 0) ∨
      Ctrl2 (matrixOfCols2 (c 0) (c 2)) (c 1) ∨
      Ctrl2 (matrixOfCols2 (c 2) (c 0)) (c 1) ∨
      Ctrl2 (matrixOfCols2 (c 0) (c 1)) (c 2) ∨
      Ctrl2 (matrixOfCols2 (c 1) (c 0)) (c 2) := by
    rcases hpair with h01 | h02 | h12
    · exact t2_six_choices_of_first_pair (c 0) (c 1) (c 2) h01
    · have h := t2_six_choices_of_first_pair (c 0) (c 2) (c 1) h02
      aesop
    · have h := t2_six_choices_of_first_pair (c 1) (c 2) (c 0) h12
      aesop
  rcases hall with h | h | h | h | h | h
  · exact ⟨0, 1, 2, by decide, by decide, by decide, h⟩
  · exact ⟨0, 2, 1, by decide, by decide, by decide, h⟩
  · exact ⟨1, 0, 2, by decide, by decide, by decide, h⟩
  · exact ⟨1, 2, 0, by decide, by decide, by decide, h⟩
  · exact ⟨2, 0, 1, by decide, by decide, by decide, h⟩
  · exact ⟨2, 1, 0, by decide, by decide, by decide, h⟩

/-- A rank-two `2 × 3` matrix has an independent pair among its columns. -/
theorem exists_independent_column_pair_of_rank_eq_two
    (R : Matrix (Fin 2) (Fin 3) K) (hR : R.rank = 2) :
    detCols2 (R.col 0) (R.col 1) ≠ 0 ∨
      detCols2 (R.col 0) (R.col 2) ≠ 0 ∨
      detCols2 (R.col 1) (R.col 2) ≠ 0 := by
  have hfin : Module.finrank K
      (Submodule.span K (Set.range R.col)) = 2 := by
    rw [← R.rank_eq_finrank_span_cols]
    exact hR
  have hspan : Submodule.span K (Set.range R.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa using hfin
  by_contra hp
  push Not at hp
  rcases hp with ⟨h01, h02, h12⟩
  let e₀ : Fin 2 → K := ![1, 0]
  let e₁ : Fin 2 → K := ![0, 1]
  have he₀ : e₀ ∈ Submodule.span K (Set.range R.col) := by
    rw [hspan]
    exact Submodule.mem_top
  have he₁ : e₁ ∈ Submodule.span K (Set.range R.col) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 he₀
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 he₁
  have h01' : R 0 0 * R 1 1 - R 1 0 * R 0 1 = 0 := by
    simpa [detCols2] using h01
  have h02' : R 0 0 * R 1 2 - R 1 0 * R 0 2 = 0 := by
    simpa [detCols2] using h02
  have h12' : R 0 1 * R 1 2 - R 1 1 * R 0 2 = 0 := by
    simpa [detCols2] using h12
  have hz : detCols2 (∑ i, q i • R.col i) (∑ i, r i • R.col i) = 0 := by
    simp only [Fin.sum_univ_three]
    simp [detCols2]
    linear_combination
      (q 0 * r 1 - q 1 * r 0) * h01' +
      (q 0 * r 2 - q 2 * r 0) * h02' +
      (q 1 * r 2 - q 2 * r 1) * h12'
  rw [hq, hr] at hz
  simp [e₀, e₁, detCols2] at hz

/-- T₂ exactly in matrix-rank form. -/
theorem t2_rank_two_matrix (R : Matrix (Fin 2) (Fin 3) K)
    (hR : R.rank = 2) :
    ∃ j k l : Fin 3, j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      Ctrl2 (matrixOfCols2 (R.col k) (R.col l)) (R.col j) :=
  t2_three_columns_of_pair R.col
    (exists_independent_column_pair_of_rank_eq_two R hR)

/-- Deleting the first row of an invertible three-by-three matrix leaves a
rank-two matrix. -/
theorem rank_deleteFirstRow_eq_two (A : Matrix (Fin 3) (Fin 3) K)
    (hA : IsUnit A.det) : (deleteFirstRow A).rank = 2 := by
  have hrows : LinearIndependent K A.row :=
    Matrix.linearIndependent_rows_of_det_ne_zero hA.ne_zero
  have hsub : LinearIndependent K (deleteFirstRow A).row := by
    change LinearIndependent K (fun r : Fin 2 => fun j => A r.succ j)
    exact hrows.comp Fin.succ (Fin.succ_injective 2)
  simpa using hsub.rank_matrix

/-- The cyclic-vector corollary at the first coordinate. -/
theorem kourovka_16_95_n3_e0 (A : Matrix (Fin 3) (Fin 3) K)
    (hA : IsUnit A.det) :
    ∃ σ : Equiv.Perm (Fin 3), Ctrl3 (A * σ.permMatrix K) ![1, 0, 0] := by
  let R := deleteFirstRow A
  have hR : R.rank = 2 := by
    simpa only [R] using rank_deleteFirstRow_eq_two A hA
  obtain ⟨j, k, l, hjk, hjl, hkl, hctrl⟩ := t2_rank_two_matrix R hR
  have hkj : k ≠ j := Ne.symm hjk
  have hlj : l ≠ j := Ne.symm hjl
  have hlk : l ≠ k := Ne.symm hkl
  let p : Fin 3 → Fin 3 := ![j, k, l]
  have hpinj : Function.Injective p := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp_all [p]
  have hpbij : Function.Bijective p :=
    ⟨hpinj, Finite.injective_iff_surjective.mp hpinj⟩
  let ρ : Equiv.Perm (Fin 3) := Equiv.ofBijective p hpbij
  let σ : Equiv.Perm (Fin 3) := ρ.symm
  let M := A * σ.permMatrix K
  have hρ0 : ρ 0 = j := by simp [ρ, p]
  have hρ1 : ρ 1 = k := by simp [ρ, p]
  have hρ2 : ρ 2 = l := by simp [ρ, p]
  have hb : dropFirst (M *ᵥ ![1, 0, 0]) = R.col j := by
    ext r
    fin_cases r <;>
      simp [dropFirst, M, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        mul_permMatrix_apply, σ, hρ0, R, deleteFirstRow]
  have hblock : lowerBlock M = matrixOfCols2 (R.col k) (R.col l) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [lowerBlock, M, matrixOfCols2, mul_permMatrix_apply, σ,
        hρ1, hρ2, R, deleteFirstRow]
  refine ⟨σ, ?_⟩
  apply ctrl3_e0_of_ctrl2_lowerBlock M
  rw [hb, hblock]
  exact hctrl

/-- Coordinatewise cyclic-vector form: every standard basis vector can be
made cyclic by a suitable column permutation. -/
theorem kourovka_16_95_n3_every_coordinate
    (A : Matrix (Fin 3) (Fin 3) K) (hA : IsUnit A.det) (i : Fin 3) :
    ∃ σ : Equiv.Perm (Fin 3), Ctrl3 (A * σ.permMatrix K) (Pi.single i 1) := by
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 i
  let Q : Matrix (Fin 3) (Fin 3) K := τ.permMatrix K
  have hQQ : Q * Q = 1 := by
    simpa only [Q, τ, Matrix.swap] using
      Matrix.swap_mul_self (R := K) (0 : Fin 3) i
  have hQunit : IsUnit Q := by
    rw [isUnit_iff_exists_inv]
    exact ⟨Q, hQQ⟩
  have hAunit : IsUnit A := A.isUnit_iff_isUnit_det.mpr hA
  let B : Matrix (Fin 3) (Fin 3) K := Q * A * Q
  have hBunit : IsUnit B := by
    exact (hQunit.mul hAunit).mul hQunit
  have hBdet : IsUnit B.det := B.isUnit_iff_isUnit_det.mp hBunit
  obtain ⟨ρ, hρ⟩ := kourovka_16_95_n3_e0 B hBdet
  let σ : Equiv.Perm (Fin 3) := τ * ρ * τ
  have htransport := ctrl3_conjugate Q Q (B * ρ.permMatrix K)
    ![1, 0, 0] hQQ hρ
  have hmat : Q * (B * ρ.permMatrix K) * Q = A * σ.permMatrix K := by
    calc
      Q * (B * ρ.permMatrix K) * Q =
          (Q * Q) * A * (Q * ρ.permMatrix K * Q) := by
            simp only [B]
            noncomm_ring
      _ = A * (Q * ρ.permMatrix K * Q) := by rw [hQQ, Matrix.one_mul]
      _ = A * σ.permMatrix K := by
        simp only [σ, τ, Q, Matrix.permMatrix_mul]
        noncomm_ring
  have hvec : Q *ᵥ ![1, 0, 0] = Pi.single i 1 := by
    simpa only [Q, τ] using swap_permMatrix_mulVec_e0 (K := K) i
  rw [hmat, hvec] at htransport
  exact ⟨σ, htransport⟩

/-- Kourovka 16.95 for `n = 3`, in cyclic-vector form.  In fact the proof
always takes the cyclic vector to be the first standard basis vector. -/
theorem kourovka_16_95_n3_cyclic_vector
    (A : Matrix (Fin 3) (Fin 3) K) (hA : IsUnit A.det) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ v : Fin 3 → K,
      LinearIndependent K
        ![v, (A * σ.permMatrix K) *ᵥ v,
          (A * σ.permMatrix K) *ᵥ ((A * σ.permMatrix K) *ᵥ v)] := by
  obtain ⟨σ, hσ⟩ := kourovka_16_95_n3_e0 A hA
  exact ⟨σ, ![1, 0, 0], by simpa only [Ctrl3] using hσ⟩

#print axioms mul_permMatrix_apply
#print axioms matrixOfCols2_mulVec
#print axioms detCols2_control_identity
#print axioms ctrl2_iff_detCols2_ne_zero
#print axioms linearIndependent_pair_iff_detCols2_ne_zero
#print axioms linearIndependent_e0_of_det_dropFirst_ne_zero
#print axioms ctrl3_e0_of_ctrl2_lowerBlock
#print axioms ctrl3_conjugate
#print axioms swap_permMatrix_mulVec_e0
#print axioms exists_pair_coordinates
#print axioms t2_six_choices_scalar
#print axioms t2_six_choices_of_first_pair
#print axioms t2_three_columns_of_pair
#print axioms exists_independent_column_pair_of_rank_eq_two
#print axioms t2_rank_two_matrix
#print axioms rank_deleteFirstRow_eq_two
#print axioms kourovka_16_95_n3_e0
#print axioms kourovka_16_95_n3_every_coordinate
#print axioms kourovka_16_95_n3_cyclic_vector

end K1695
