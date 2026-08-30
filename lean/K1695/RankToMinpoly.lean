import K1695.RankCriterion
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Dual

open scoped Matrix

namespace K1695

open Matrix Polynomial Module

universe u

/-- Over an algebraically closed field, an endomorphism whose dual eigenspaces
all have dimension at most one has a cyclic vector.  We record cyclicity as
surjectivity of polynomial evaluation at that vector. -/
theorem exists_cyclic_vector_of_dual_eigenspace_finrank_le_one
    {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V)
    (hgeom : ∀ mu : K,
      finrank K (Module.End.eigenspace
        (f.dualMap : Module.End K (Module.Dual K V)) mu) ≤ 1) :
    ∃ v : V, LinearMap.range
      ((LinearMap.applyₗ (R := K) v).comp (Polynomial.aeval f).toLinearMap) = ⊤ := by
  classical
  let fd : Module.End K (Module.Dual K V) := f.dualMap
  let phi : fd.Eigenvalues → Module.Dual K V := fun mu ↦
    (Module.End.HasEigenvalue.exists_hasEigenvector mu.property).choose
  have hphi_eigen (mu : fd.Eigenvalues) :
      fd.HasEigenvector mu (phi mu) :=
    (Module.End.HasEigenvalue.exists_hasEigenvector mu.property).choose_spec
  have hphi_nonzero (mu : fd.Eigenvalues) : phi mu ≠ 0 :=
    (hphi_eigen mu).2
  have hphi_detect (mu : fd.Eigenvalues) : ∃ x : V, phi mu x ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    apply hphi_nonzero mu
    ext x
    simpa using h x
  obtain ⟨v, hv⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists phi hphi_detect
  refine ⟨v, ?_⟩
  let e : K[X] →ₗ[K] V :=
    (LinearMap.applyₗ (R := K) v).comp (Polynomial.aeval f).toLinearMap
  let W : Submodule K V := LinearMap.range e
  change W = ⊤
  have hWinv : ∀ x ∈ W, f x ∈ W := by
    rintro x ⟨p, rfl⟩
    refine ⟨Polynomial.X * p, ?_⟩
    simp [e, Module.End.mul_apply]
  by_contra hW
  have hWann_ne : W.dualAnnihilator ≠ ⊥ := by
    simpa using hW
  let _ : Nontrivial W.dualAnnihilator :=
    Submodule.nontrivial_iff_ne_bot.mpr hWann_ne
  have hdualInv : ∀ psi ∈ W.dualAnnihilator,
      f.dualMap psi ∈ W.dualAnnihilator := by
    intro psi hpsi
    rw [Submodule.mem_dualAnnihilator] at hpsi ⊢
    intro x hx
    exact hpsi (f x) (hWinv x hx)
  let g : Module.End K W.dualAnnihilator := f.dualMap.restrict hdualInv
  obtain ⟨mu, hmu⟩ := Module.End.exists_eigenvalue
    (K := K) (V := W.dualAnnihilator) g
  obtain ⟨psi, hpsi⟩ :=
    Module.End.HasEigenvalue.exists_hasEigenvector hmu
  have hpsi_eq : f.dualMap (psi : Module.Dual K V) = mu • (psi : Module.Dual K V) := by
    have := hpsi.apply_eq_smul
    exact congrArg Subtype.val this
  have hpsi_mem : (psi : Module.Dual K V) ∈ fd.eigenspace mu :=
    Module.End.mem_eigenspace_iff.mpr hpsi_eq
  have hpsi_ne : (psi : Module.Dual K V) ≠ 0 := by
    exact Subtype.coe_ne_coe.mpr hpsi.2
  let emu : fd.Eigenvalues :=
    ⟨mu, Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr ⟨hpsi_mem, hpsi_ne⟩)⟩
  have hphi_mem : phi emu ∈ fd.eigenspace mu := by
    exact (hphi_eigen emu).1
  have hdim : finrank K (fd.eigenspace mu) = 1 := by
    apply le_antisymm (hgeom mu)
    exact Submodule.one_le_finrank_iff.mpr
      ((fd.eigenspace mu).ne_bot_iff.mpr
        ⟨phi emu, hphi_mem, hphi_nonzero emu⟩)
  let xphi : fd.eigenspace mu := ⟨phi emu, hphi_mem⟩
  let xpsi : fd.eigenspace mu := ⟨(psi : Module.Dual K V), hpsi_mem⟩
  have xphi_ne : xphi ≠ 0 := by
    intro hx
    apply hphi_nonzero emu
    exact congrArg Subtype.val hx
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim
    xphi_ne xpsi
  have hc' : c • phi emu = (psi : Module.Dual K V) := congrArg Subtype.val hc
  have hvW : v ∈ W := by
    refine ⟨1, ?_⟩
    simp [e]
  have hpsi_ann : ∀ x ∈ W, (psi : Module.Dual K V) x = 0 := by
    rw [← Submodule.mem_dualAnnihilator]
    exact psi.2
  have hpsiv : (psi : Module.Dual K V) v = 0 := hpsi_ann v hvW
  have hcv : c * phi emu v = 0 := by
    have hcval := congrArg (fun q : Module.Dual K V ↦ q v) hc'
    rw [hpsiv] at hcval
    simpa using hcval
  have hc0 : c = 0 := (mul_eq_zero.mp hcv).resolve_right (hv emu)
  apply hpsi_ne
  rw [← hc', hc0, zero_smul]

/-- A cyclic vector in the polynomial-evaluation sense forces the minimal
polynomial of an endomorphism to have at least the ambient dimension. -/
theorem finrank_le_natDegree_minpoly_of_eval_range_eq_top
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (v : V)
    (hcyc : LinearMap.range
      ((LinearMap.applyₗ (R := K) v).comp (Polynomial.aeval f).toLinearMap) = ⊤) :
    finrank K V ≤ (minpoly K f).natDegree := by
  classical
  let d := (minpoly K f).natDegree
  let S : Submodule K V := Submodule.span K
    (Set.range fun i : Fin d ↦ (f ^ (i : ℕ)) v)
  have htop : S = ⊤ := by
    apply top_unique
    intro y _
    have hy : y ∈ LinearMap.range
        ((LinearMap.applyₗ (R := K) v).comp (Polynomial.aeval f).toLinearMap) := by
      rw [hcyc]
      exact Submodule.mem_top
    obtain ⟨p, hp⟩ := LinearMap.mem_range.mp hy
    rw [← hp]
    have hend : Polynomial.aeval f p ∈ Submodule.span K
        (Set.range fun i : Fin d ↦ f ^ (i : ℕ)) := by
      apply IsIntegral.mem_span_pow (Algebra.IsIntegral.isIntegral f)
      exact ⟨p, rfl⟩
    refine Submodule.span_induction (p := fun q _ ↦ q v ∈ S) ?_ ?_ ?_ ?_ hend
    · rintro q ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · simp [S]
    · intro x y _ _ hx hy
      simpa using Submodule.add_mem S hx hy
    · intro c x _ hx
      simpa using Submodule.smul_mem S c hx
  have hle : finrank K V ≤ Fintype.card (Fin d) := by
    apply finrank_le_of_span_eq_top
    exact htop
  simpa [d] using hle

/-- Scalar extension of a matrix is annihilated by the image of its
base-field minimal polynomial. -/
theorem aeval_map_minpoly_eq_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) K) :
    Polynomial.aeval (B.map (algebraMap K L))
      ((minpoly K B).map (algebraMap K L)) = 0 := by
  classical
  let Phi : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) L :=
    (algebraMap K L).mapMatrix
  have hcomp :
      (algebraMap L (Matrix (Fin n) (Fin n) L)).comp (algebraMap K L) =
        Phi.comp (algebraMap K (Matrix (Fin n) (Fin n) K)) := by
    ext c i j
    by_cases hij : i = j <;>
      simp [Phi, Matrix.algebraMap_matrix_apply, hij]
  have hz := congrArg Phi (minpoly.aeval K B)
  rw [Polynomial.map_aeval_eq_aeval_map hcomp] at hz
  simpa [Phi] using hz

/-- Outside the roots of the mapped minimal polynomial, a scalar shift of a
matrix has full rank. -/
theorem rank_map_sub_scalar_eq_of_not_isRoot_map_minpoly
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) K) (mu : L)
    (hnotroot : ¬Polynomial.IsRoot
      ((minpoly K B).map (algebraMap K L)) mu) :
    (B.map (algebraMap K L) - mu • 1).rank = n := by
  classical
  let C : Matrix (Fin n) (Fin n) L := B.map (algebraMap K L)
  let f : Module.End L (Fin n → L) := Matrix.toLin' C
  let q : Module.End L (Fin n → L) := Matrix.toLin' (C - mu • 1)
  have hshift : f - mu • 1 = q := by
    ext x i
    simp [f, q, C, Matrix.toLin'_apply]
  have hzero : Polynomial.aeval C
      ((minpoly K B).map (algebraMap K L)) = 0 := by
    simpa only [C] using aeval_map_minpoly_eq_zero (L := L) B
  have hdvd : minpoly L C ∣ (minpoly K B).map (algebraMap K L) :=
    minpoly.dvd L C hzero
  by_contra hfull
  have hrankle : (C - mu • 1).rank ≤ n := by
    simpa using Matrix.rank_le_width (C - mu • 1)
  have hranklt : (C - mu • 1).rank < n := by
    have hne : (C - mu • 1).rank ≠ n := by
      simpa only [C] using hfull
    omega
  have hrange : finrank L (LinearMap.range q) = (C - mu • 1).rank := by
    rfl
  have hnull := LinearMap.finrank_range_add_finrank_ker q
  rw [hrange] at hnull
  have hfin : finrank L (Fin n → L) = n := by simp
  rw [hfin] at hnull
  have hkerpos : 0 < finrank L (LinearMap.ker q) := by omega
  have hkerne : LinearMap.ker q ≠ ⊥ :=
    Submodule.one_le_finrank_iff.mp hkerpos
  have heig : f.HasEigenvalue mu := by
    rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_def, hshift]
    exact hkerne
  have hroot : Polynomial.IsRoot (minpoly L C) mu := by
    have := Module.End.isRoot_of_hasEigenvalue heig
    rwa [Matrix.minpoly_toLin'] at this
  exact hnotroot (hroot.dvd hdvd)

/-- The dimension-free rank-to-minimal-polynomial bridge.  It is enough to
impose the rank hypothesis after extension to one algebraically closed field. -/
theorem minpoly_eq_charpoly_of_rank_ge_algClosed
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (n : ℕ) (B : Matrix (Fin n) (Fin n) K)
    (h : ∀ mu : L,
      n - 1 ≤ (B.map (algebraMap K L) - mu • 1).rank) :
    minpoly K B = B.charpoly := by
  classical
  let C : Matrix (Fin n) (Fin n) L := B.map (algebraMap K L)
  let f : Module.End L (Fin n → L) := Matrix.toLin' C
  have hgeom (mu : L) : finrank L (Module.End.eigenspace
      (f.dualMap : Module.End L (Module.Dual L (Fin n → L))) mu) ≤ 1 := by
    let q : Module.End L (Fin n → L) := Matrix.toLin' (C - mu • 1)
    have hshift : (f.dualMap : Module.End L (Module.Dual L (Fin n → L))) - mu • 1 =
        q.dualMap := by
      ext psi x
      simp [f, q, C, Matrix.toLin'_apply]
    rw [Module.End.eigenspace_def, hshift]
    have hrange : finrank L (LinearMap.range q.dualMap) =
        (C - mu • 1).rank := by
      rw [LinearMap.finrank_range_dualMap_eq_finrank_range]
      rfl
    have hnull := LinearMap.finrank_range_add_finrank_ker q.dualMap
    rw [hrange] at hnull
    have hrank : n - 1 ≤ (C - mu • 1).rank := by
      simpa only [C] using h mu
    have hdualfin : finrank L (Module.Dual L (Fin n → L)) = n := by simp
    rw [hdualfin] at hnull
    omega
  obtain ⟨v, hv⟩ :=
    exists_cyclic_vector_of_dual_eigenspace_finrank_le_one f hgeom
  have hdegLower : n ≤ (minpoly L C).natDegree := by
    have := finrank_le_natDegree_minpoly_of_eval_range_eq_top f v hv
    rw [Matrix.minpoly_toLin'] at this
    simpa using this
  have hdegUpper : (minpoly L C).natDegree ≤ n := by
    have hdvd := Matrix.minpoly_dvd_charpoly C
    have hle := Polynomial.natDegree_le_of_dvd hdvd
      (Matrix.charpoly_monic C).ne_zero
    simpa using hle
  have hdegC : (minpoly L C).natDegree = n :=
    le_antisymm hdegUpper hdegLower
  have hzero : Polynomial.aeval C ((minpoly K B).map (algebraMap K L)) = 0 := by
    simpa only [C] using aeval_map_minpoly_eq_zero (L := L) B
  have hdvd : minpoly L C ∣ (minpoly K B).map (algebraMap K L) :=
    minpoly.dvd L C hzero
  have hdegBaseLower : n ≤ (minpoly K B).natDegree := by
    have hle := Polynomial.natDegree_le_of_dvd hdvd
      ((minpoly.monic (Algebra.IsIntegral.isIntegral B)).map
        (algebraMap K L)).ne_zero
    rw [hdegC] at hle
    simpa using hle
  have hdegBaseUpper : (minpoly K B).natDegree ≤ n := by
    have hle := Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly B)
      (Matrix.charpoly_monic B).ne_zero
    simpa using hle
  exact minpoly_eq_charpoly_of_natDegree_eq B
    (le_antisymm hdegBaseUpper hdegBaseLower)

/-- Ticket-facing version: a rank bound valid in every field extension may
be specialized to an algebraic closure. -/
theorem minpoly_eq_charpoly_of_rank_ge
    {K : Type u} [Field K]
    (n : ℕ) (B : Matrix (Fin n) (Fin n) K)
    (h : ∀ (L : Type u) [Field L] [Algebra K L] (mu : L),
      n - 1 ≤ (B.map (algebraMap K L) - mu • 1).rank) :
    minpoly K B = B.charpoly := by
  apply minpoly_eq_charpoly_of_rank_ge_algClosed
    (L := AlgebraicClosure K) n B
  intro mu
  exact h (AlgebraicClosure K) mu

/-- Backwards-compatible `4 × 4` specialization. -/
theorem minpoly_eq_charpoly_of_rank_ge_four_algClosed
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (B : Matrix (Fin 4) (Fin 4) K)
    (h : ∀ mu : L, 3 ≤ (B.map (algebraMap K L) - mu • 1).rank) :
    minpoly K B = B.charpoly :=
  minpoly_eq_charpoly_of_rank_ge_algClosed 4 B h

/-- Backwards-compatible ticket-facing `4 × 4` specialization. -/
theorem minpoly_eq_charpoly_of_rank_ge_four
    {K : Type u} [Field K]
    (B : Matrix (Fin 4) (Fin 4) K)
    (h : ∀ (L : Type u) [Field L] [Algebra K L] (mu : L),
      3 ≤ (B.map (algebraMap K L) - mu • 1).rank) :
    minpoly K B = B.charpoly :=
  minpoly_eq_charpoly_of_rank_ge 4 B h

#print axioms minpoly_eq_charpoly_of_rank_ge_algClosed
#print axioms minpoly_eq_charpoly_of_rank_ge

end K1695
