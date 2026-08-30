import K1695.RankToMinpoly
import K1695.StratumBAssembly

open scoped Matrix

namespace K1695

open Matrix Polynomial

universe u

/-- Kourovka 16.95 on stratum (b), in the minimal-polynomial form, for
`4 × 4` matrices.  The rank theorem from `StratumBAssembly` supplies the
hypothesis of the algebraic-closure rank-to-minimal-polynomial bridge. -/
theorem stratumB_minpoly
    {F : Type u} [Field F]
    (A : Matrix (Fin 4) (Fin 4) F) (hA : IsUnit A.det)
    (m : F[X]) (hm : Irreducible m) (hdeg : m.natDegree = 2)
    (hmin : minpoly F A = m) (a b : Fin 4) (hab : a ≠ b) :
    minpoly F (A * Matrix.swap F a b) =
      (A * Matrix.swap F a b).charpoly := by
  apply minpoly_eq_charpoly_of_rank_ge_four (A * Matrix.swap F a b)
  intro L _ _ mu
  have hrank := stratumB_rank_form A hA m hm hdeg hmin a b hab mu
  have hmap :
      (A * Matrix.swap F a b).map (algebraMap F L) =
        A.map (algebraMap F L) * Matrix.swap L a b := by
    rw [Matrix.map_mul, Matrix.map_swap]
  simpa only [hmap] using hrank

#print axioms stratumB_minpoly

end K1695
