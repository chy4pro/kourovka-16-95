import K1695.CyclicVectorThree

open scoped Matrix

namespace K1695

open Matrix Polynomial

variable {K : Type*} [Field K]

/-- A Krylov-cyclic vector forces the minimal polynomial of a matrix to be
its characteristic polynomial. -/
theorem minpoly_eq_charpoly_of_krylov_linearIndependent {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (h : LinearIndependent K (fun k : Fin n ↦ (M ^ (k : ℕ)) *ᵥ v)) :
    minpoly K M = M.charpoly := by
  apply minpoly.eq_of_linearIndependent (A := K) (x := M) (p := M.charpoly)
    (Matrix.charpoly_monic M) (Matrix.aeval_self_charpoly M) n
  · simp
  · apply Fintype.linearIndependent_iff.mpr
    intro g hg i
    apply Fintype.linearIndependent_iff.mp h g
    · calc
        ∑ j, g j • ((M ^ (j : ℕ)) *ᵥ v) =
            (∑ j, g j • (M ^ (j : ℕ))) *ᵥ v := by
              simp only [Matrix.sum_mulVec, Matrix.smul_mulVec]
        _ = 0 := by rw [hg, Matrix.zero_mulVec]

/-- Kourovka 16.95 for `n = 3`, in the notebook's minimal-polynomial form. -/
theorem kourovka_16_95_n3 (A : Matrix (Fin 3) (Fin 3) K)
    (hA : IsUnit A.det) :
    ∃ σ : Equiv.Perm (Fin 3),
      minpoly K (A * σ.permMatrix K) =
        (A * σ.permMatrix K).charpoly := by
  obtain ⟨σ, v, hv⟩ := kourovka_16_95_n3_cyclic_vector A hA
  refine ⟨σ, minpoly_eq_charpoly_of_krylov_linearIndependent
    (A * σ.permMatrix K) v ?_⟩
  convert hv using 1
  funext k
  fin_cases k <;> simp [pow_two, Matrix.mulVec_mulVec]

/-- Adding arbitrary multiples of the initial vector at each step of a
Krylov recurrence does not destroy linear independence. -/
theorem krylov_feedback_linearIndependent {m : ℕ}
    (T : Matrix (Fin m) (Fin m) K) (b : Fin m → K)
    (z : ℕ → Fin m → K) (a : ℕ → K)
    (hz0 : z 0 = b)
    (hzsucc : ∀ k, z (k + 1) = T *ᵥ z k + a k • b)
    (hpow : LinearIndependent K
      (fun k : Fin m ↦ (T ^ (k : ℕ)) *ᵥ b)) :
    LinearIndependent K (fun k : Fin m ↦ z k) := by
  let u : ℕ → Fin m → K := fun k ↦ (T ^ k) *ᵥ b
  have hu0 : u 0 = b := by simp [u]
  have husucc (k : ℕ) : u (k + 1) = T *ᵥ u k := by
    simp [u, pow_succ', Matrix.mulVec_mulVec]
  have hflag : ∀ k : ℕ,
      Submodule.span K (Set.range (fun j : Fin k ↦ z (j : ℕ))) =
        Submodule.span K (Set.range (fun j : Fin k ↦ u (j : ℕ))) ∧
      z k - u k ∈
        Submodule.span K (Set.range (fun j : Fin k ↦ u (j : ℕ))) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simp
        · simp [hz0, hu0]
    | succ k ih =>
        rcases ih with ⟨hspan, hdiff⟩
        have hspan' :
            Submodule.span K
                (Set.range (fun j : Fin (k + 1) ↦ z (j : ℕ))) =
              Submodule.span K
                (Set.range (fun j : Fin (k + 1) ↦ u (j : ℕ))) := by
          apply le_antisymm
          · rw [Submodule.span_le]
            rintro x ⟨j, rfl⟩
            refine Fin.lastCases ?_ (fun q ↦ ?_) j
            · have hu_last : u k ∈ Submodule.span K
                  (Set.range (fun r : Fin (k + 1) ↦ u (r : ℕ))) :=
                Submodule.subset_span ⟨Fin.last k, by simp⟩
              have hdiff_last : z k - u k ∈ Submodule.span K
                  (Set.range (fun r : Fin (k + 1) ↦ u (r : ℕ))) := by
                apply Submodule.span_mono ?_ hdiff
                rintro _ ⟨r, rfl⟩
                exact ⟨r.castSucc, rfl⟩
              have := Submodule.add_mem _ hu_last hdiff_last
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
            · apply Submodule.span_mono ?_ (hspan.le
                  (Submodule.subset_span ⟨q, rfl⟩))
              rintro _ ⟨r, rfl⟩
              exact ⟨r.castSucc, rfl⟩
          · rw [Submodule.span_le]
            rintro x ⟨j, rfl⟩
            refine Fin.lastCases ?_ (fun q ↦ ?_) j
            · have hz_last : z k ∈ Submodule.span K
                  (Set.range (fun r : Fin (k + 1) ↦ z (r : ℕ))) :=
                Submodule.subset_span ⟨Fin.last k, by simp⟩
              have hdiff_last : z k - u k ∈ Submodule.span K
                  (Set.range (fun r : Fin (k + 1) ↦ z (r : ℕ))) := by
                apply Submodule.span_mono ?_ (hspan.ge hdiff)
                rintro _ ⟨r, rfl⟩
                exact ⟨r.castSucc, rfl⟩
              have := Submodule.sub_mem _ hz_last hdiff_last
              change u k ∈ Submodule.span K
                (Set.range (fun r : Fin (k + 1) ↦ z (r : ℕ)))
              simpa only [sub_sub_cancel] using this
            · apply Submodule.span_mono ?_ (hspan.ge
                  (Submodule.subset_span ⟨q, rfl⟩))
              rintro _ ⟨r, rfl⟩
              exact ⟨r.castSucc, rfl⟩
        refine ⟨hspan', ?_⟩
        have hTdiff : T *ᵥ (z k - u k) ∈
            Submodule.span K
              (Set.range (fun j : Fin (k + 1) ↦ u (j : ℕ))) := by
          refine Submodule.span_induction (p := fun x _ ↦ T *ᵥ x ∈
              Submodule.span K
                (Set.range (fun j : Fin (k + 1) ↦ u (j : ℕ))))
            ?_ ?_ ?_ ?_ hdiff
          · rintro x ⟨j, rfl⟩
            apply Submodule.subset_span
            exact ⟨j.succ, by simp only [Fin.val_succ]; rw [husucc]⟩
          · simp
          · intro x y _ _ hx hy
            simpa only [Matrix.mulVec_add] using Submodule.add_mem _ hx hy
          · intro c x _ hx
            simpa only [Matrix.mulVec_smul] using Submodule.smul_mem _ c hx
        have hbmem : a k • b ∈ Submodule.span K
            (Set.range (fun j : Fin (k + 1) ↦ u (j : ℕ))) := by
          apply Submodule.smul_mem
          apply Submodule.subset_span
          exact ⟨0, by simp [hu0]⟩
        rw [hzsucc, husucc]
        have heq : (T *ᵥ z k + a k • b) - T *ᵥ u k =
            T *ᵥ (z k - u k) + a k • b := by
          rw [Matrix.mulVec_sub]
          module
        rw [heq]
        exact Submodule.add_mem _ hTdiff hbmem
  cases m with
  | zero => exact linearIndependent_empty_type
  | succ m =>
      have hspan := (hflag (m + 1)).1
      apply linearIndependent_of_top_le_span_of_card_eq_finrank
      · rw [hspan]
        exact (hpow.span_eq_top_of_card_eq_finrank (by simp)).ge
      · simp

/-- Delete one coordinate from a vector, using `Fin.succAbove` to enumerate
the remaining coordinates. -/
def deleteCoordinate {m : ℕ} (i : Fin (m + 1))
    (x : Fin (m + 1) → K) : Fin m → K :=
  fun r ↦ x (i.succAbove r)

/-- Delete row `i`, retaining all columns. -/
def deleteRowExcept {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)) :
    Matrix (Fin m) (Fin (m + 1)) K :=
  fun r s ↦ A (i.succAbove r) s

/-- The principal block obtained by deleting row and column `i`. -/
def principalBlockExcept {m : ℕ}
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)) :
    Matrix (Fin m) (Fin m) K :=
  fun r s ↦ M (i.succAbove r) (i.succAbove s)

/-- Column `i` with its `i`-th entry deleted. -/
def pivotColumnExcept {m : ℕ}
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)) :
    Fin m → K :=
  fun r ↦ M (i.succAbove r) i

/-- Multiplication followed by deletion of coordinate `i` splits into the
principal-block action and a scalar multiple of the deleted pivot column. -/
theorem deleteCoordinate_mulVec {m : ℕ}
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1))
    (x : Fin (m + 1) → K) :
    deleteCoordinate i (M *ᵥ x) =
      principalBlockExcept M i *ᵥ deleteCoordinate i x +
        x i • pivotColumnExcept M i := by
  ext r
  simp only [deleteCoordinate, principalBlockExcept, pivotColumnExcept,
    Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply]
  rw [Fin.sum_univ_succAbove]
  ring

/-- General deflation bridge: cyclicity of the principal block at the
deleted pivot column implies cyclicity of the corresponding standard basis
vector for the full matrix.  Taking `m + 1 = n` is the `(S') ⟸ (Tₙ₋₁)`
step. -/
theorem cyclic_standardBasis_of_principalBlock {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (σ : Equiv.Perm (Fin (m + 1))) (i : Fin (m + 1))
    (hctrl : LinearIndependent K (fun k : Fin m ↦
      ((principalBlockExcept (A * σ.permMatrix K) i) ^ (k : ℕ)) *ᵥ
        pivotColumnExcept (A * σ.permMatrix K) i)) :
    LinearIndependent K (fun k : Fin (m + 1) ↦
      (((A * σ.permMatrix K) ^ (k : ℕ)) *ᵥ Pi.single i 1)) := by
  let B : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    A * σ.permMatrix K
  let T : Matrix (Fin m) (Fin m) K := principalBlockExcept B i
  let b : Fin m → K := pivotColumnExcept B i
  let e : Fin (m + 1) → K := Pi.single i 1
  let y : ℕ → Fin (m + 1) → K := fun k ↦ (B ^ k) *ᵥ e
  let z : ℕ → Fin m → K := fun k ↦ deleteCoordinate i (y (k + 1))
  let a : ℕ → K := fun k ↦ y (k + 1) i
  have hy0 : y 0 = e := by simp [y]
  have hysucc (k : ℕ) : y (k + 1) = B *ᵥ y k := by
    simp [y, pow_succ', Matrix.mulVec_mulVec]
  have hedrop : deleteCoordinate i e = 0 := by
    ext r
    simp [deleteCoordinate, e, Fin.succAbove_ne]
  have hei : e i = 1 := by simp [e]
  have hz0 : z 0 = b := by
    rw [show z 0 = deleteCoordinate i (B *ᵥ e) by
      simp [z, y]]
    rw [deleteCoordinate_mulVec, hedrop, Matrix.mulVec_zero, hei,
      one_smul, zero_add]
  have hzsucc (k : ℕ) : z (k + 1) = T *ᵥ z k + a k • b := by
    change deleteCoordinate i (y (k + 1 + 1)) =
      T *ᵥ deleteCoordinate i (y (k + 1)) + y (k + 1) i • b
    rw [show k + 1 + 1 = (k + 1) + 1 by omega, hysucc,
      deleteCoordinate_mulVec]
  have hzLI : LinearIndependent K (fun k : Fin m ↦ z (k : ℕ)) := by
    apply krylov_feedback_linearIndependent T b z a hz0 hzsucc
    simpa only [T, b, B] using hctrl
  change LinearIndependent K (fun k : Fin (m + 1) ↦ y (k : ℕ))
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  have htail : ∑ k : Fin m, g k.succ • z (k : ℕ) = 0 := by
    ext r
    simp only [z, Finset.sum_apply, deleteCoordinate, Pi.zero_apply, Pi.smul_apply]
    change ∑ k : Fin m, g k.succ * y ((k : ℕ) + 1) (i.succAbove r) = 0
    have hr := congrFun hg (i.succAbove r)
    rw [Fin.sum_univ_succ] at hr
    have hyzero : y ((0 : Fin (m + 1)) : ℕ) = e := by simpa using hy0
    rw [hyzero] at hr
    simpa [e, Fin.succAbove_ne] using hr
  have hsucc : ∀ k : Fin m, g k.succ = 0 := by
    exact Fintype.linearIndependent_iff.mp hzLI (fun k ↦ g k.succ) htail
  have hg0 : g 0 = 0 := by
    have hi := congrFun hg i
    rw [Fin.sum_univ_succ] at hi
    have hyzero : y ((0 : Fin (m + 1)) : ℕ) = e := by simpa using hy0
    rw [hyzero] at hi
    simpa [e, hsucc] using hi
  exact Fin.cases hg0 hsucc

/-- The `n = 4` instance of the cyclic-vector/minimal-polynomial bridge. -/
example (M : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → K)
    (h : LinearIndependent K (fun k : Fin 4 ↦ (M ^ (k : ℕ)) *ᵥ v)) :
    minpoly K M = M.charpoly :=
  minpoly_eq_charpoly_of_krylov_linearIndependent M v h

/-- The `n = 4` instance of general deflation. -/
example (A : Matrix (Fin 4) (Fin 4) K) (σ : Equiv.Perm (Fin 4))
    (i : Fin 4)
    (hctrl : LinearIndependent K (fun k : Fin 3 ↦
      ((principalBlockExcept (A * σ.permMatrix K) i) ^ (k : ℕ)) *ᵥ
        pivotColumnExcept (A * σ.permMatrix K) i)) :
    LinearIndependent K (fun k : Fin 4 ↦
      ((A * σ.permMatrix K) ^ (k : ℕ)) *ᵥ Pi.single i 1) :=
  cyclic_standardBasis_of_principalBlock A σ i hctrl

#print axioms minpoly_eq_charpoly_of_krylov_linearIndependent
#print axioms kourovka_16_95_n3
#print axioms krylov_feedback_linearIndependent
#print axioms deleteCoordinate_mulVec
#print axioms cyclic_standardBasis_of_principalBlock

end K1695
