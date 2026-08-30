import K1695.RankToMinpoly

open scoped Matrix

namespace K1695

open Matrix Polynomial

universe u

/-- Dimension-generic final assembly for a transposition.  This theorem
isolates the only remaining input in the general stratum-(b) argument: the
rank form over every scalar extension. -/
theorem minpoly_mul_swap_eq_charpoly_of_rank_form
    {F : Type u} [Field F] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) F) (a b : Fin n)
    (hrank : ∀ (L : Type u) [Field L] [Algebra F L] (mu : L),
      n - 1 ≤
        (A.map (algebraMap F L) * Matrix.swap L a b - mu • 1).rank) :
    minpoly F (A * Matrix.swap F a b) =
      (A * Matrix.swap F a b).charpoly := by
  apply minpoly_eq_charpoly_of_rank_ge n (A * Matrix.swap F a b)
  intro L _ _ mu
  have hmap :
      (A * Matrix.swap F a b).map (algebraMap F L) =
        A.map (algebraMap F L) * Matrix.swap L a b := by
    rw [Matrix.map_mul, Matrix.map_swap]
  simpa only [hmap] using hrank L mu

/-- Even-dimensional specialization of the generic assembly.  It is stated
separately so a future module-theoretic proof of the stratum-(b) rank form can
be plugged in without changing the final theorem layer. -/
theorem stratumB_minpoly_general_of_rank_form
    {F : Type u} [Field F] (k : ℕ)
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) F) (a b : Fin (2 * k))
    (hrank : ∀ (L : Type u) [Field L] [Algebra F L] (mu : L),
      2 * k - 1 ≤
        (A.map (algebraMap F L) * Matrix.swap L a b - mu • 1).rank) :
    minpoly F (A * Matrix.swap F a b) =
      (A * Matrix.swap F a b).charpoly :=
  minpoly_mul_swap_eq_charpoly_of_rank_form (2 * k) A a b hrank

/-- In every dimension, it is enough to prove the transposition rank bound at
roots of the mapped minimal polynomial.  Away from those roots the original
shift has full rank, and the general rank-one transposition bound applies. -/
theorem stratumB_rank_form_general_of_root_rank
    {F : Type u} [Field F] (k : ℕ)
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) F)
    (m : F[X]) (hmin : minpoly F A = m)
    (a b : Fin (2 * k)) (hab : a ≠ b)
    (hrootRank : ∀ (L : Type u) [Field L] [Algebra F L] (mu : L),
      Polynomial.IsRoot (m.map (algebraMap F L)) mu →
        2 * k - 1 ≤
          (A.map (algebraMap F L) * Matrix.swap L a b - mu • 1).rank) :
    ∀ (L : Type u) [Field L] [Algebra F L] (mu : L),
      2 * k - 1 ≤
        (A.map (algebraMap F L) * Matrix.swap L a b - mu • 1).rank := by
  intro L _ _ mu
  by_cases hroot : Polynomial.IsRoot (m.map (algebraMap F L)) mu
  · exact hrootRank L mu hroot
  · have hnotroot : ¬Polynomial.IsRoot
        ((minpoly F A).map (algebraMap F L)) mu := by
      simpa only [hmin] using hroot
    have hfull := rank_map_sub_scalar_eq_of_not_isRoot_map_minpoly A mu hnotroot
    change 2 * k - 1 ≤
      (A.map (algebraMap F L) *
        transpositionMatrix (K := L) a b - mu • 1).rank
    exact l4_t0 (A.map (algebraMap F L)) mu a b hab hfull

/-- General even-dimensional stratum-(b) assembly with only the root case
left as an explicit input.  The irreducibility and degree assumptions are
included in the statement expected by the hand theorem; they are precisely
the data from which the missing module-theoretic root-rank lemma must be
derived. -/
theorem stratumB_minpoly_general_of_root_rank
    {F : Type u} [Field F] (k : ℕ)
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) F) (_hA : IsUnit A.det)
    (m : F[X]) (_hm : Irreducible m) (_hdeg : m.natDegree = k)
    (hmin : minpoly F A = m) (a b : Fin (2 * k)) (hab : a ≠ b)
    (hrootRank : ∀ (L : Type u) [Field L] [Algebra F L] (mu : L),
      Polynomial.IsRoot (m.map (algebraMap F L)) mu →
        2 * k - 1 ≤
          (A.map (algebraMap F L) * Matrix.swap L a b - mu • 1).rank) :
    minpoly F (A * Matrix.swap F a b) =
      (A * Matrix.swap F a b).charpoly := by
  have hrank := stratumB_rank_form_general_of_root_rank
    k A m hmin a b hab hrootRank
  exact stratumB_minpoly_general_of_rank_form k A a b hrank

#print axioms minpoly_mul_swap_eq_charpoly_of_rank_form
#print axioms stratumB_minpoly_general_of_rank_form
#print axioms stratumB_rank_form_general_of_root_rank
#print axioms stratumB_minpoly_general_of_root_rank

end K1695
