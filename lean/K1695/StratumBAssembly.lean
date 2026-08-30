import K1695.StratumB
import K1695.RankCriterion

open scoped Matrix

namespace K1695

open Matrix Polynomial

/-- Matrix rank is unchanged by applying a homomorphism between fields. -/
theorem rank_map_eq_of_field_hom {K L : Type*} [Field K] [Field L]
    {n : ℕ} (f : K →+* L) (M : Matrix (Fin n) (Fin n) K) :
    (M.map f).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form M
  have hVmap : IsUnit (V.map f) := hV.map f.mapMatrix
  have hUmap : IsUnit (U.map f) := hU.map f.mapMatrix
  have hVdet : IsUnit (V.map f).det := (Matrix.isUnit_iff_isUnit_det _).1 hVmap
  have hUdet : IsUnit (U.map f).det := (Matrix.isUnit_iff_isUnit_det _).1 hUmap
  have hnormalMap := congrArg (fun N => N.map f) hnormal
  simp only [Matrix.map_mul] at hnormalMap
  calc
    (M.map f).rank = (V.map f * M.map f * U.map f).rank := by
      symm
      rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUdet,
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVdet]
    _ = (((Matrix.fromBlocks 1 0 0 0).submatrix e e).map f).rank :=
      congrArg Matrix.rank hnormalMap
    _ = M.rank := by
      have hmapBlock :
          ((Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) K) 0 0 0).submatrix e e).map f =
            (Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) L) 0 0 0).submatrix e e := by
        ext i j
        simp only [Matrix.map_apply, Matrix.submatrix_apply]
        rcases e i with i | i <;> rcases e j with j | j <;>
          simp [Matrix.fromBlocks, Matrix.one_apply]
      rw [hmapBlock]
      rw [Matrix.rank_submatrix]
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal,
        Matrix.rank_diagonal]
      let g : Fin M.rank →
          {x : Fin M.rank ⊕ Fin (Fintype.card (Fin n) - M.rank) //
            Sum.elim (fun _ => (1 : L)) (fun _ => 0) x ≠ 0} :=
        fun i => ⟨Sum.inl i, by simp⟩
      have hg : Function.Bijective g := by
        constructor
        · intro i j hij
          exact Sum.inl_injective (congrArg Subtype.val hij)
        · rintro ⟨i | j, h⟩
          · exact ⟨i, rfl⟩
          · simp at h
      let nzEquiv := Equiv.ofBijective g hg
      simpa using (Fintype.card_congr nzEquiv).symm

/-- The exact root rank from `StratumB` holds in an arbitrary ambient field
extension.  We apply the simple-extension result over `F⟨μ⟩` and use rank
invariance under the inclusion `F⟨μ⟩ → L`. -/
theorem stratumB_rank_at_root
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (A : Matrix (Fin 4) (Fin 4) F) (hA : IsUnit A.det)
    (m : F[X]) (hm : Irreducible m) (hdeg : m.natDegree = 2)
    (hmin : minpoly F A = m) (mu : L)
    (hroot : Polynomial.IsRoot (m.map (algebraMap F L)) mu)
    (a b : Fin 4) (hab : a ≠ b) :
    (A.map (algebraMap F L) * Matrix.swap L a b - mu • 1).rank = 3 := by
  let E := IntermediateField.adjoin F ({mu} : Set L)
  let muE : E := IntermediateField.AdjoinSimple.gen F mu
  have hmonic : m.Monic := by
    rw [← hmin]
    exact minpoly.monic (Algebra.IsIntegral.isIntegral A)
  have hroot' : Polynomial.aeval mu m = 0 := by
    rw [Polynomial.IsRoot, Polynomial.eval_map] at hroot
    simpa only [Polynomial.aeval_def] using hroot
  have hmuint : IsIntegral F mu := ⟨m, hmonic, hroot'⟩
  have hmuEint : IsIntegral F muE := by
    rw [show muE = IntermediateField.AdjoinSimple.gen F mu by rfl]
    exact (IntermediateField.AdjoinSimple.isIntegral_gen F mu).2 hmuint
  have hminmu : minpoly F mu = m := by
    exact (minpoly.eq_of_irreducible_of_monic hm hroot' hmonic).symm
  have hmuEdeg : (minpoly F muE).natDegree = 2 := by
    rw [show muE = IntermediateField.AdjoinSimple.gen F mu by rfl,
      IntermediateField.minpoly_gen, hminmu, hdeg]
  have hrootE : Polynomial.IsRoot (m.map (algebraMap F E)) muE := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    change Polynomial.aeval muE m = 0
    rw [← hminmu]
    exact IntermediateField.aeval_gen_minpoly F mu
  let pb : PowerBasis F E := IntermediateField.adjoin.powerBasis hmuint
  have hpbgen : pb.gen = muE := by
    rfl
  have hadjoin : Algebra.adjoin F ({muE} : Set E) = ⊤ := by
    simpa only [hpbgen] using pb.adjoin_gen_eq_top
  have hrootRank :
      (A.map (algebraMap F E) * Matrix.swap E a b - muE • 1).rank = 3 :=
    stratumB_rank_at_root_of_simple_extension
      A hA m hm hdeg hmin muE hmuEint hadjoin hmuEdeg hrootE a b hab
  have hmap :
      ((A.map (algebraMap F E) * Matrix.swap E a b - muE • 1).map
        (algebraMap E L)).rank = 3 := by
    rw [rank_map_eq_of_field_hom, hrootRank]
  have hmatrix :
      (A.map (algebraMap F E) * Matrix.swap E a b - muE • 1).map
          (algebraMap E L) =
        A.map (algebraMap F L) * Matrix.swap L a b - mu • 1 := by
    change (algebraMap E L).mapMatrix
        (A.map (algebraMap F E) * Matrix.swap E a b - muE • 1) = _
    rw [map_sub, map_mul]
    have hAmap : (algebraMap E L).mapMatrix (A.map (algebraMap F E)) =
        A.map (algebraMap F L) := by
      ext i j
      simp
    have hswap : (algebraMap E L).mapMatrix (Matrix.swap E a b) =
        Matrix.swap L a b := Matrix.map_swap (algebraMap E L) a b
    have hscalar : (algebraMap E L).mapMatrix
        (muE • (1 : Matrix (Fin 4) (Fin 4) E)) =
          mu • (1 : Matrix (Fin 4) (Fin 4) L) := by
      ext i j
      by_cases hij : i = j <;> simp [muE, hij]
    rw [hAmap, hswap, hscalar]
  rwa [hmatrix] at hmap

/-- Away from the roots of the quadratic minimal polynomial, the unpermuted
shift has full rank, so the transposition estimate loses at most one rank. -/
theorem stratumB_rank_at_nonroot
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (A : Matrix (Fin 4) (Fin 4) F)
    (m : F[X]) (hdeg : m.natDegree = 2)
    (hmin : minpoly F A = m) (mu : L)
    (hnotroot : Polynomial.aeval mu m ≠ 0)
    (a b : Fin 4) (hab : a ≠ b) :
    3 ≤ (A.map (algebraMap F L) * Matrix.swap L a b - mu • 1).rank := by
  have hmonic : m.Monic := by
    rw [← hmin]
    exact minpoly.monic (Algebra.IsIntegral.isIntegral A)
  let s : F := -m.coeff 0
  let t : F := -m.coeff 1
  have hmform : m =
      Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X - Polynomial.C s := by
    simpa only [s, t] using monic_quadratic_normal_form m hmonic hdeg
  have hnquad : mu * mu ≠ algebraMap F L s + algebraMap F L t * mu := by
    intro hquad
    apply hnotroot
    rw [hmform]
    simp only [map_sub, map_pow, aeval_X, aeval_C, map_mul]
    linear_combination hquad
  have hzero : A * A - t • A - s • 1 = 0 :=
    quadratic_annihilator_of_minpoly A s t (hmin.trans hmform)
  exact quadratic_nonroot_transposition_rank_ge_three
    A mu s t hnquad hzero a b hab

/-- Rank-form assembly of stratum (b), valid over every field extension and
at every scalar. -/
theorem stratumB_rank_form
    {F : Type*} [Field F]
    (A : Matrix (Fin 4) (Fin 4) F) (hA : IsUnit A.det)
    (m : F[X]) (hm : Irreducible m) (hdeg : m.natDegree = 2)
    (hmin : minpoly F A = m) (a b : Fin 4) (hab : a ≠ b)
    {L : Type*} [Field L] [Algebra F L] (mu : L) :
    3 ≤ (A.map (algebraMap F L) * Matrix.swap L a b - mu • 1).rank := by
  by_cases heval : Polynomial.aeval mu m = 0
  · have hroot : Polynomial.IsRoot (m.map (algebraMap F L)) mu := by
      rw [Polynomial.IsRoot, Polynomial.eval_map]
      simpa only [Polynomial.aeval_def] using heval
    rw [stratumB_rank_at_root A hA m hm hdeg hmin mu hroot a b hab]
  · exact stratumB_rank_at_nonroot A m hdeg hmin mu heval a b hab

private noncomputable def zmod3Quadratic : (ZMod 3)[X] := Polynomial.X ^ 2 + 1

/-- Two companion blocks for `X² + 1` over `ZMod 3`. -/
private def zmod3CompanionBlocks : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![0, -1, 0, 0;
     1,  0, 0, 0;
     0,  0, 0, -1;
     0,  0, 1, 0]

/-- Concrete specialization to `C_(X²+1) ⊕ C_(X²+1)` over `ZMod 3`. -/
theorem zmod3_companion_blocks_rank_form
    {L : Type*} [Field L] [Algebra (ZMod 3) L]
    (mu : L) (a b : Fin 4) (hab : a ≠ b) :
    3 ≤ (zmod3CompanionBlocks.map (algebraMap (ZMod 3) L) *
      Matrix.swap L a b - mu • 1).rank := by
  have hm : Irreducible zmod3Quadratic := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [zmod3Quadratic, ← Polynomial.C_1,
        Polynomial.natDegree_X_pow_add_C]
      norm_num
    · intro x
      simp only [Polynomial.IsRoot, zmod3Quadratic, Polynomial.eval_add,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
      fin_cases x <;> decide
  have hdeg : zmod3Quadratic.natDegree = 2 := by
    rw [zmod3Quadratic, ← Polynomial.C_1,
      Polynomial.natDegree_X_pow_add_C]
  have hdet : zmod3CompanionBlocks.det = 1 := by decide
  have hunit : IsUnit zmod3CompanionBlocks.det := by
    rw [hdet]
    exact isUnit_one
  have hzero : Polynomial.aeval zmod3CompanionBlocks zmod3Quadratic = 0 := by
    simp only [zmod3Quadratic, map_add, map_pow, Polynomial.aeval_X, map_one]
    decide
  have hmonic : zmod3Quadratic.Monic := by
    rw [zmod3Quadratic, ← Polynomial.C_1]
    exact Polynomial.monic_X_pow_add_C (1 : ZMod 3) (by decide : 2 ≠ 0)
  have hmin : minpoly (ZMod 3) zmod3CompanionBlocks = zmod3Quadratic :=
    (minpoly.eq_of_irreducible_of_monic hm hzero hmonic).symm
  exact stratumB_rank_form zmod3CompanionBlocks hunit zmod3Quadratic
    hm hdeg hmin a b hab mu

example {L : Type*} [Field L] [Algebra (ZMod 3) L]
    (mu : L) (a b : Fin 4) (hab : a ≠ b) :
    3 ≤ (zmod3CompanionBlocks.map (algebraMap (ZMod 3) L) *
      Matrix.swap L a b - mu • 1).rank :=
  zmod3_companion_blocks_rank_form mu a b hab

#print axioms rank_map_eq_of_field_hom
#print axioms stratumB_rank_at_root
#print axioms stratumB_rank_at_nonroot
#print axioms stratumB_rank_form
#print axioms zmod3_companion_blocks_rank_form

end K1695
