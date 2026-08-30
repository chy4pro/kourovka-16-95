import Mathlib

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

open Matrix Finset Equiv BigOperators
open scoped Classical

variable {K : Type*} [Field K]

def br (u v : K × K) : K := u.1 * v.2 - u.2 * v.1

lemma br_anti (u v : K × K) : br v u = -br u v := by
  simp [br]
  ring

def Delta (a b c : K × K) : K := a.1 * br a b + a.2 * br a c

def e1Vec : Fin 3 → K := ![1, 0, 0]

def colPerm (A : Matrix (Fin 3) (Fin 3) K) (σ : Equiv.Perm (Fin 3)) :
    Matrix (Fin 3) (Fin 3) K := fun i j => A i (σ j)

def deltaSix (x0 x1 x2 : K × K) : Fin 6 → K := fun i =>
  match i.val with
  | 0 => Delta x0 x1 x2
  | 1 => Delta x0 x2 x1
  | 2 => Delta x1 x0 x2
  | 3 => Delta x1 x2 x0
  | 4 => Delta x2 x0 x1
  | 5 => Delta x2 x1 x0
  | _ => 0

def permOfIndex : Fin 6 → Equiv.Perm (Fin 3) := fun i =>
  match i.val with
  | 0 => Equiv.refl (Fin 3)
  | 1 => Equiv.swap 1 2
  | 2 => Equiv.swap 0 1
  | 3 => (Equiv.swap 1 2).trans (Equiv.swap 0 1)
  | 4 => (Equiv.swap 0 1).trans (Equiv.swap 1 2)
  | 5 => Equiv.swap 0 2
  | _ => Equiv.refl (Fin 3)

def indexOfPerm (σ : Equiv.Perm (Fin 3)) : Fin 6 :=
  if σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 then 0
  else if σ 0 = 0 ∧ σ 1 = 2 ∧ σ 2 = 1 then 1
  else if σ 0 = 1 ∧ σ 1 = 0 ∧ σ 2 = 2 then 2
  else if σ 0 = 1 ∧ σ 1 = 2 ∧ σ 2 = 0 then 3
  else if σ 0 = 2 ∧ σ 1 = 0 ∧ σ 2 = 1 then 4
  else 5

lemma indexOfPerm_permOfIndex (i : Fin 6) : indexOfPerm (permOfIndex i) = i := by
  fin_cases i <;>
    simp (config := {decide := true}) [indexOfPerm, permOfIndex, Equiv.refl_apply,
      Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne]

lemma permOfIndex_injective : Function.Injective permOfIndex := by
  intro i j h
  have := congr_arg indexOfPerm h
  simpa [indexOfPerm_permOfIndex] using this

lemma two_le_card_of_two_mem {α : Type*} [DecidableEq α] {s : Finset α} {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : 2 ≤ s.card := by
  classical
  have hsub : ({a, b} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard : ({a, b} : Finset α).card = 2 := by
    simp [Finset.card_insert_of_notMem, hab]
  have := Finset.card_le_card hsub
  linarith

lemma det_e1_aux (v w : Fin 3 → K) :
    Matrix.det (![e1Vec, v, w] : Matrix (Fin 3) (Fin 3) K) = v 1 * w 2 - v 2 * w 1 := by
  let M : Matrix (Fin 3) (Fin 3) K := ![e1Vec, v, w]
  change Matrix.det M = v 1 * w 2 - v 2 * w 1
  rw [Matrix.det_fin_three M]
  simp [M, e1Vec]

lemma colPerm_mulVec_e1 (A : Matrix (Fin 3) (Fin 3) K) (σ : Equiv.Perm (Fin 3)) :
    (colPerm A σ).mulVec e1Vec = fun r => A r (σ 0) := by
  ext r
  simp (config := {decide := true}) [colPerm, e1Vec, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val', Matrix.vecHead, Matrix.vecTail]

lemma colPerm_sq_mulVec_e1 (A : Matrix (Fin 3) (Fin 3) K) (σ : Equiv.Perm (Fin 3)) :
    ((colPerm A σ) * (colPerm A σ)).mulVec e1Vec = fun r =>
      A r (σ 0) * A 0 (σ 0) + A r (σ 1) * A 1 (σ 0) + A r (σ 2) * A 2 (σ 0) := by
  ext r
  simp (config := {decide := true}) [colPerm, e1Vec, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val', Matrix.vecHead, Matrix.vecTail]

lemma det_colPerm_krylov_eq_Delta (A : Matrix (Fin 3) (Fin 3) K) (σ : Equiv.Perm (Fin 3)) :
    Matrix.det (![e1Vec, (colPerm A σ).mulVec e1Vec,
      ((colPerm A σ) * (colPerm A σ)).mulVec e1Vec] : Matrix (Fin 3) (Fin 3) K) =
    Delta (A 1 (σ 0), A 2 (σ 0)) (A 1 (σ 1), A 2 (σ 1)) (A 1 (σ 2), A 2 (σ 2)) := by
  rw [det_e1_aux]
  simp only [colPerm_mulVec_e1, colPerm_sq_mulVec_e1]
  simp [Delta, br]
  ring

lemma pair_zero_algebra (p q r s u v : K)
    (h0 : p * (p * s - q * r) + q * (p * v - q * u) = 0)
    (h1 : p * (p * v - q * u) + q * (p * s - q * r) = 0)
    (h2 : -r * (p * s - q * r) + s * (r * v - s * u) = 0)
    (h3 : r * (r * v - s * u) - s * (p * s - q * r) = 0)
    (hspan : (p * s - q * r) ≠ 0 ∨ (p * v - q * u) ≠ 0 ∨ (r * v - s * u) ≠ 0) :
    (-(u * (p * v - q * u)) - v * (r * v - s * u) ≠ 0) ∧
    (-(u * (r * v - s * u)) - v * (p * v - q * u) ≠ 0) := by
  set A := p * s - q * r with hA
  set B := p * v - q * u with hB
  set C := r * v - s * u with hC
  have h0' : p * A + q * B = 0 := by simpa [hA, hB] using h0
  have h1' : p * B + q * A = 0 := by simpa [hA, hB] using h1
  have h2' : -r * A + s * C = 0 := by simpa [hA, hC] using h2
  have h3' : r * C - s * A = 0 := by simpa [hA, hC] using h3
  have hspan' : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0 := by simpa [hA, hB, hC] using hspan
  have hAne : A ≠ 0 := by
    by_contra hA0
    have hB0 : B = 0 := by
      by_contra hBne
      have hp : p = 0 := by
        have : p * B = 0 := by simpa [hA0] using h1'
        exact (mul_eq_zero.mp this).resolve_right hBne
      have hq : q = 0 := by
        have : q * B = 0 := by simpa [hA0] using h0'
        exact (mul_eq_zero.mp this).resolve_right hBne
      have : B = 0 := by simp [hB, hp, hq]
      contradiction
    have hC0 : C = 0 := by
      by_contra hCne
      have hr : r = 0 := by
        have : r * C = 0 := by simpa [hA0] using h3'
        exact (mul_eq_zero.mp this).resolve_right hCne
      have hs : s = 0 := by
        have : s * C = 0 := by simpa [hA0] using h2'
        exact (mul_eq_zero.mp this).resolve_right hCne
      have : C = 0 := by simp [hC, hr, hs]
      contradiction
    rcases hspan' with hA' | hB' | hC'
    · exact hA' hA0
    · exact hB' hB0
    · exact hC' hC0
  have hAsq_ne : A ^ 2 ≠ 0 := by
    intro h
    have : A * A = 0 := by simpa [pow_two] using h
    rcases mul_eq_zero.mp this with hA' | hA' <;> exact hAne hA'
  have hp0 : p ≠ 0 := by
    intro hp
    have hq : q = 0 := by
      have : q * A = 0 := by simpa [hp] using h1'
      exact (mul_eq_zero.mp this).resolve_right hAne
    have : A = 0 := by simp [hA, hp, hq]
    exact hAne this
  have hq0 : q ≠ 0 := by
    intro hq
    have hp : p = 0 := by
      have : p * A = 0 := by simpa [hq] using h0'
      exact (mul_eq_zero.mp this).resolve_right hAne
    have : A = 0 := by simp [hA, hp, hq]
    exact hAne this
  have hr0 : r ≠ 0 := by
    intro hr
    have hs : s = 0 := by
      have : s * A = 0 := by
        have : -s * A = 0 := by simpa [hr] using h3'
        simpa [neg_mul] using this
      exact (mul_eq_zero.mp this).resolve_right hAne
    have : A = 0 := by simp [hA, hr, hs]
    exact hAne this
  have hs0 : s ≠ 0 := by
    intro hs
    have hr : r = 0 := by
      have : r * A = 0 := by
        have : -r * A = 0 := by simpa [hs] using h2'
        simpa [neg_mul] using this
      exact (mul_eq_zero.mp this).resolve_right hAne
    have : A = 0 := by simp [hA, hr, hs]
    exact hAne this
  have hpq : p = q ∨ p = -q := by
    have hpq_mul : (p ^ 2 - q ^ 2) * A = 0 := by
      linear_combination p * h0' - q * h1'
    have hpq_sq : p ^ 2 = q ^ 2 := by
      have : p ^ 2 - q ^ 2 = 0 := (mul_eq_zero.mp hpq_mul).resolve_right hAne
      exact sub_eq_zero.mp this
    have hfac : (p - q) * (p + q) = 0 := by
      have hsub : p ^ 2 - q ^ 2 = 0 := sub_eq_zero.mpr hpq_sq
      ring_nf
      simpa [pow_two] using hsub
    rcases mul_eq_zero.mp hfac with h | h
    · left; exact sub_eq_zero.mp h
    · right
      rw [← sub_eq_zero]
      linear_combination h
  have hrs : r = s ∨ r = -s := by
    have hrs_mul : (s ^ 2 - r ^ 2) * A = 0 := by
      linear_combination r * h2' - s * h3'
    have hrs_sq : r ^ 2 = s ^ 2 := by
      have h : s ^ 2 = r ^ 2 := sub_eq_zero.mp ((mul_eq_zero.mp hrs_mul).resolve_right hAne)
      exact h.symm
    have hfac : (r - s) * (r + s) = 0 := by
      have hsub : r ^ 2 - s ^ 2 = 0 := sub_eq_zero.mpr hrs_sq
      ring_nf
      simpa [pow_two] using hsub
    rcases mul_eq_zero.mp hfac with h | h
    · left; exact sub_eq_zero.mp h
    · right
      rw [← sub_eq_zero]
      linear_combination h
  suffices hgoal : (-(u * B) - v * C ≠ 0) ∧ (-(u * C) - v * B ≠ 0) by
    simpa [hB, hC] using hgoal
  rcases hpq with hpq | hpq <;> rcases hrs with hrs | hrs
  · -- p = q, r = s
    have hBneg : B = -A := by
      have htmp : q * A + q * B = 0 := by simpa [hpq] using h0'
      have hsum : p * (A + B) = 0 := by
        rw [hpq]
        ring_nf
        exact htmp
      have hAB : A + B = 0 := (mul_eq_zero.mp hsum).resolve_left hp0
      rw [← sub_eq_zero]
      linear_combination hAB
    have hCpos : C = A := by
      have htmp : r * C - r * A = 0 := by simpa [hrs] using h3'
      have hmul : r * (C - A) = 0 := by
        linear_combination htmp
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hr0)
    have hBexpr : B = p * (v - u) := by
      simp [hB, hpq]
      ring
    have hp_vu : p * (v - u) = -A := by rw [← hBexpr, hBneg]
    have hp_uv : p * (u - v) = A := by
      have : p * (u - v) = -(p * (v - u)) := by ring
      rw [this, hp_vu]
      ring
    have hD4 : p * (-(u * B) - v * C) = A ^ 2 := by
      calc
        p * (-(u * B) - v * C) = p * (u * A - v * A) := by rw [hBneg, hCpos]; ring
        _ = A * (p * (u - v)) := by ring
        _ = A * A := by rw [hp_uv]
        _ = A ^ 2 := by ring
    have hD5 : p * (-(u * C) - v * B) = -A ^ 2 := by
      calc
        p * (-(u * C) - v * B) = p * (-(u * A) + v * A) := by rw [hCpos, hBneg]; ring
        _ = A * (p * (v - u)) := by ring
        _ = A * (-A) := by rw [hp_vu]
        _ = -A ^ 2 := by ring
    exact ⟨fun h => hAsq_ne (by simpa [h] using hD4.symm),
           fun h => hAsq_ne (neg_eq_zero.mp (by simpa [h] using hD5.symm))⟩
  · -- p = q, r = -s
    have hBneg : B = -A := by
      have htmp : q * A + q * B = 0 := by simpa [hpq] using h0'
      have hsum : p * (A + B) = 0 := by
        rw [hpq]
        ring_nf
        exact htmp
      have hAB : A + B = 0 := (mul_eq_zero.mp hsum).resolve_left hp0
      rw [← sub_eq_zero]
      linear_combination hAB
    have hCneg : C = -A := by
      have htmp : s * A + s * C = 0 := by
        have := h2'
        simp [hrs] at this
        ring_nf at this
        exact this
      have hsum : s * (A + C) = 0 := by
        linear_combination htmp
      have hAC : A + C = 0 := (mul_eq_zero.mp hsum).resolve_left hs0
      rw [← sub_eq_zero]
      linear_combination hAC
    have hBexpr : B = p * (v - u) := by
      simp [hB, hpq]
      ring
    have hp_vu : p * (v - u) = -A := by rw [← hBexpr, hBneg]
    have hCexpr : C = -s * (u + v) := by
      simp [hC, hrs]
      ring
    have hsum : s * (u + v) = A := by
      have : -s * (u + v) = -A := by rw [← hCexpr, hCneg]
      simpa using this
    have hD4 : s * (-(u * B) - v * C) = A ^ 2 := by
      calc
        s * (-(u * B) - v * C) = s * (u * A + v * A) := by rw [hBneg, hCneg]; ring
        _ = A * (s * (u + v)) := by ring
        _ = A * A := by rw [hsum]
        _ = A ^ 2 := by ring
    have hD5 : s * (-(u * C) - v * B) = A ^ 2 := by
      calc
        s * (-(u * C) - v * B) = s * (u * A + v * A) := by rw [hCneg, hBneg]; ring
        _ = A * (s * (u + v)) := by ring
        _ = A ^ 2 := by rw [hsum]; ring
    exact ⟨fun h => hAsq_ne (by simpa [h] using hD4.symm),
           fun h => hAsq_ne (by simpa [h] using hD5.symm)⟩
  · -- p = -q, r = s
    have hBpos : B = A := by
      have htmp : q * B - q * A = 0 := by
        have := h0'
        simp [hpq] at this
        ring_nf at this
        linear_combination this
      have hmul : q * (B - A) = 0 := by
        linear_combination htmp
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hq0)
    have hCpos : C = A := by
      have htmp : r * C - r * A = 0 := by simpa [hrs] using h3'
      have hmul : r * (C - A) = 0 := by
        linear_combination htmp
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hr0)
    have hBexpr : B = p * (u + v) := by
      simp [hB, hpq]
      ring
    have hpsum : p * (u + v) = A := by rw [← hBexpr, hBpos]
    have hD4 : p * (-(u * B) - v * C) = -A ^ 2 := by
      calc
        p * (-(u * B) - v * C) = p * (-(u * A) - v * A) := by rw [hBpos, hCpos]
        _ = -A * (p * (u + v)) := by ring
        _ = -A * A := by rw [hpsum]
        _ = -A ^ 2 := by ring
    have hD5 : p * (-(u * C) - v * B) = -A ^ 2 := by
      calc
        p * (-(u * C) - v * B) = p * (-(u * A) - v * A) := by rw [hCpos, hBpos]
        _ = -A * (p * (u + v)) := by ring
        _ = -A ^ 2 := by rw [hpsum]; ring
    exact ⟨fun h => hAsq_ne (neg_eq_zero.mp (by simpa [h] using hD4.symm)),
           fun h => hAsq_ne (neg_eq_zero.mp (by simpa [h] using hD5.symm))⟩
  · -- p = -q, r = -s is incompatible with A ≠ 0
    have : A = 0 := by
      simp [hA, hpq, hrs]
    exact False.elim (hAne this)

lemma Delta_pair_zero (a b c : K × K)
    (h0 : Delta a b c = 0) (h1 : Delta a c b = 0)
    (h2 : Delta b a c = 0) (h3 : Delta b c a = 0)
    (hspan : br a b ≠ 0 ∨ br a c ≠ 0 ∨ br b c ≠ 0) :
    Delta c a b ≠ 0 ∧ Delta c b a ≠ 0 := by
  rcases a with ⟨p, q⟩
  rcases b with ⟨r, s⟩
  rcases c with ⟨u, v⟩
  have h0eq : Delta (p, q) (r, s) (u, v) = p * (p * s - q * r) + q * (p * v - q * u) := by
    simp [Delta, br]
  have h1eq : Delta (p, q) (u, v) (r, s) = p * (p * v - q * u) + q * (p * s - q * r) := by
    simp [Delta, br]
  have h2eq : Delta (r, s) (p, q) (u, v) = -r * (p * s - q * r) + s * (r * v - s * u) := by
    simp [Delta, br]
    ring
  have h3eq : Delta (r, s) (u, v) (p, q) = r * (r * v - s * u) - s * (p * s - q * r) := by
    simp [Delta, br]
    ring
  have h0a : p * (p * s - q * r) + q * (p * v - q * u) = 0 := by
    rw [h0eq] at h0
    exact h0
  have h1a : p * (p * v - q * u) + q * (p * s - q * r) = 0 := by
    rw [h1eq] at h1
    exact h1
  have h2a : -r * (p * s - q * r) + s * (r * v - s * u) = 0 := by
    rw [h2eq] at h2
    exact h2
  have h3a : r * (r * v - s * u) - s * (p * s - q * r) = 0 := by
    rw [h3eq] at h3
    exact h3
  have hspana : (p * s - q * r) ≠ 0 ∨ (p * v - q * u) ≠ 0 ∨ (r * v - s * u) ≠ 0 := by
    simpa [br] using hspan
  have hall := pair_zero_algebra p q r s u v h0a h1a h2a h3a hspana
  have hD4eq : Delta (u, v) (p, q) (r, s) = -(u * (p * v - q * u)) - v * (r * v - s * u) := by
    simp [Delta, br]
    ring
  have hD5eq : Delta (u, v) (r, s) (p, q) = -(u * (r * v - s * u)) - v * (p * v - q * u) := by
    simp [Delta, br]
    ring
  exact ⟨by rw [hD4eq]; exact hall.1, by rw [hD5eq]; exact hall.2⟩

lemma pair_not_zero_choice {x y : K} (h : ¬(x = 0 ∧ y = 0)) : x ≠ 0 ∨ y ≠ 0 := by
  by_cases hx : x = 0
  · right
    intro hy
    exact h ⟨hx, hy⟩
  · left
    exact hx

lemma deltaSix_eq_Delta_permOfIndex (x : Fin 3 → K × K) (i : Fin 6) :
    Delta (x ((permOfIndex i) 0)) (x ((permOfIndex i) 1)) (x ((permOfIndex i) 2)) =
      deltaSix (x 0) (x 1) (x 2) i := by
  fin_cases i <;>
    simp (config := {decide := true}) [deltaSix, permOfIndex, Equiv.refl_apply,
      Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne]

lemma exists_two_deltaSix_ne_zero (x0 x1 x2 : K × K)
    (hspan : br x0 x1 ≠ 0 ∨ br x0 x2 ≠ 0 ∨ br x1 x2 ≠ 0) :
    ∃ i j : Fin 6, i ≠ j ∧ deltaSix x0 x1 x2 i ≠ 0 ∧ deltaSix x0 x1 x2 j ≠ 0 := by
  classical
  have hspan210 : br x2 x0 ≠ 0 ∨ br x2 x1 ≠ 0 ∨ br x0 x1 ≠ 0 := by
    rcases hspan with h | h | h
    · right; right; exact h
    · left
      intro hz
      apply h
      rw [br_anti] at hz
      exact neg_eq_zero.mp hz
    · right; left
      intro hz
      apply h
      rw [br_anti] at hz
      exact neg_eq_zero.mp hz
  have hspan120 : br x1 x2 ≠ 0 ∨ br x1 x0 ≠ 0 ∨ br x2 x0 ≠ 0 := by
    rcases hspan with h | h | h
    · right; left
      intro hz
      apply h
      rw [br_anti] at hz
      exact neg_eq_zero.mp hz
    · right; right
      intro hz
      apply h
      rw [br_anti] at hz
      exact neg_eq_zero.mp hz
    · left; exact h
  by_cases hP0 : deltaSix x0 x1 x2 0 = 0 ∧ deltaSix x0 x1 x2 1 = 0
  · by_cases hP1 : deltaSix x0 x1 x2 2 = 0 ∧ deltaSix x0 x1 x2 3 = 0
    · have hne := Delta_pair_zero x0 x1 x2 hP0.1 hP0.2 hP1.1 hP1.2 hspan
      exact ⟨4, 5, by decide, by simpa [deltaSix] using hne.1, by simpa [deltaSix] using hne.2⟩
    · by_cases hP2 : deltaSix x0 x1 x2 4 = 0 ∧ deltaSix x0 x1 x2 5 = 0
      · have hne := Delta_pair_zero x2 x0 x1 hP2.1 hP2.2 hP0.2 hP0.1 hspan210
        exact ⟨2, 3, by decide, by simpa [deltaSix] using hne.2, by simpa [deltaSix] using hne.1⟩
      · have h1 := pair_not_zero_choice hP1
        have h2 := pair_not_zero_choice hP2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact ⟨2, 4, by decide, h1, h2⟩
        · exact ⟨2, 5, by decide, h1, h2⟩
        · exact ⟨3, 4, by decide, h1, h2⟩
        · exact ⟨3, 5, by decide, h1, h2⟩
  · by_cases hP1 : deltaSix x0 x1 x2 2 = 0 ∧ deltaSix x0 x1 x2 3 = 0
    · by_cases hP2 : deltaSix x0 x1 x2 4 = 0 ∧ deltaSix x0 x1 x2 5 = 0
      · have hne := Delta_pair_zero x1 x2 x0 hP1.2 hP1.1 hP2.2 hP2.1 hspan120
        exact ⟨0, 1, by decide, by simpa [deltaSix] using hne.1, by simpa [deltaSix] using hne.2⟩
      · have h0 := pair_not_zero_choice hP0
        have h2 := pair_not_zero_choice hP2
        rcases h0 with h0 | h0 <;> rcases h2 with h2 | h2
        · exact ⟨0, 4, by decide, h0, h2⟩
        · exact ⟨0, 5, by decide, h0, h2⟩
        · exact ⟨1, 4, by decide, h0, h2⟩
        · exact ⟨1, 5, by decide, h0, h2⟩
    · have h0 := pair_not_zero_choice hP0
      have h1 := pair_not_zero_choice hP1
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
      · exact ⟨0, 2, by decide, h0, h1⟩
      · exact ⟨0, 3, by decide, h0, h1⟩
      · exact ⟨1, 2, by decide, h0, h1⟩
      · exact ⟨1, 3, by decide, h0, h1⟩

lemma deltaSix_count_ge_two (x0 x1 x2 : K × K)
    (hspan : br x0 x1 ≠ 0 ∨ br x0 x2 ≠ 0 ∨ br x1 x2 ≠ 0) :
    2 ≤ (Finset.univ.filter (fun i : Fin 6 => deltaSix x0 x1 x2 i ≠ 0)).card := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ := exists_two_deltaSix_ne_zero x0 x1 x2 hspan
  have hi_mem : i ∈ Finset.univ.filter (fun i => deltaSix x0 x1 x2 i ≠ 0) := by
    simpa [hi]
  have hj_mem : j ∈ Finset.univ.filter (fun i => deltaSix x0 x1 x2 i ≠ 0) := by
    simpa [hj]
  exact two_le_card_of_two_mem hi_mem hj_mem hij

theorem goodCount3 (K : Type*) [Field K] (A : Matrix (Fin 3) (Fin 3) K) (hA : IsUnit A.det) :
    2 ≤ (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) =>
      Matrix.det (![e1Vec, (colPerm A σ) *ᵥ e1Vec,
        ((colPerm A σ) * (colPerm A σ)) *ᵥ e1Vec] : Matrix (Fin 3) (Fin 3) K) ≠ 0)).card := by
  classical
  let x : Fin 3 → K × K := fun j => (A 1 j, A 2 j)
  have hdet_ne : A.det ≠ 0 := by
    simpa [isUnit_iff_ne_zero] using hA
  have hdet_expand :
      A.det = A 0 0 * br (x 1) (x 2) - A 0 1 * br (x 0) (x 2) + A 0 2 * br (x 0) (x 1) := by
    simp [x]
    rw [Matrix.det_fin_three]
    simp [br]
    ring
  have hspan : br (x 0) (x 1) ≠ 0 ∨ br (x 0) (x 2) ≠ 0 ∨ br (x 1) (x 2) ≠ 0 := by
    by_contra h
    have h1 : br (x 0) (x 1) = 0 := by
      by_contra hn
      exact h (Or.inl hn)
    have h2 : br (x 0) (x 2) = 0 := by
      by_contra hn
      exact h (Or.inr (Or.inl hn))
    have h3 : br (x 1) (x 2) = 0 := by
      by_contra hn
      exact h (Or.inr (Or.inr hn))
    have : A.det = 0 := by
      rw [hdet_expand, h1, h2, h3]
      ring
    exact hdet_ne this
  obtain ⟨i, j, hij, hi, hj⟩ := exists_two_deltaSix_ne_zero (x 0) (x 1) (x 2) hspan
  let P : Equiv.Perm (Fin 3) → Prop := fun σ =>
    Matrix.det (![e1Vec, (colPerm A σ) *ᵥ e1Vec,
      ((colPerm A σ) * (colPerm A σ)) *ᵥ e1Vec] : Matrix (Fin 3) (Fin 3) K) ≠ 0
  have hi_mem : permOfIndex i ∈ Finset.univ.filter P := by
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [det_colPerm_krylov_eq_Delta]
    have hEq :
        Delta (A 1 ((permOfIndex i) 0), A 2 ((permOfIndex i) 0))
          (A 1 ((permOfIndex i) 1), A 2 ((permOfIndex i) 1))
          (A 1 ((permOfIndex i) 2), A 2 ((permOfIndex i) 2)) =
        deltaSix (x 0) (x 1) (x 2) i := by
      have := deltaSix_eq_Delta_permOfIndex x i
      simpa [x] using this
    rw [hEq]
    exact hi
  have hj_mem : permOfIndex j ∈ Finset.univ.filter P := by
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [det_colPerm_krylov_eq_Delta]
    have hEq :
        Delta (A 1 ((permOfIndex j) 0), A 2 ((permOfIndex j) 0))
          (A 1 ((permOfIndex j) 1), A 2 ((permOfIndex j) 1))
          (A 1 ((permOfIndex j) 2), A 2 ((permOfIndex j) 2)) =
        deltaSix (x 0) (x 1) (x 2) j := by
      have := deltaSix_eq_Delta_permOfIndex x j
      simpa [x] using this
    rw [hEq]
    exact hj
  have hσ : permOfIndex i ≠ permOfIndex j := by
    intro h
    exact hij (permOfIndex_injective h)
  exact two_le_card_of_two_mem hi_mem hj_mem hσ

#print axioms goodCount3
