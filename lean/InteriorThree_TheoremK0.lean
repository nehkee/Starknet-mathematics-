import InteriorThree_LemmaCG

/-!
# Theorem K0 (rukafe0x, result 29), in Lean

Target `LEMMA` (tier 3, `problem-3a-upper`). The `k = 0` cells (`Q = q0` constant) with `h > 4D`:
over a field where every positive integer up to `4h` is nonzero, with `e = 2h - D`, `1 ≤ D`, `4D < h`,
there is no `A` (monic, degree `h`), `B` (degree `≤ h`, `B(0) ≠ 0`) and `q0 ≠ 0` with
`A ^ 3 + X ^ e B ^ 3 = q0 (X ^ (e + 2h) A + B)`.

Route (polynomials only; result 29's fourth roots are replaced by truncations):
1. Lemma S: `B² M = (2hA + θA) R - A θR` with `M = 3AθB - BθA - 2hAB`, so `deg M ≤ D`, and
   `M ≡ 2(θ - h)(AB) mod X^e`; hence `AB ≡ Λ = L0 + c X^h (mod X^e)` with `deg L0 ≤ D`.
2. `A⁴ ≡ q0 Λ (mod X^e)` gives `X^e ∣ 4ΛθA - θΛ·A = P + c X^h (4θA - hA)`, `P = 4L0θA - θL0·A`.
   If `c = 0`, `P = 0`, and its top coefficient `(4h - deg L0) lead L0` is not `0`.
3. If `c ≠ 0`: `A_j = 0` for `D < j < h - D`, `4j ≠ h`; the truncation `a` of `A` below `h - D` has
   `4L0θa = θL0·a` exactly, so `4 deg a = deg L0 ≤ D`; then `a⁴ = q0 L0` and `4a³A_high = q0 c X^D`
   exactly, so `a` is constant and `A = X^h + a0`.
4. Then `B = b0 + b_h X^h` and the coefficient of `X^(3h)` in `A³ = q0 B + X^e R` gives `R_(h+D) = 1`,
   while `B³ + R = q0 X^(2h) A` gives `R_(h+D) = 0`.
-/

namespace TheoremK0

open Polynomial LemmaCG

variable {K : Type*} [Field K]

theorem natDegree_wronski4_le {p q : K[X]} {a b : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (4 * p * theta q - theta p * q).natDegree ≤ a + b := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans (add_le_add ?_ ((natDegree_theta_le q).trans hq))
    refine natDegree_mul_le.trans ?_
    simpa using hp
  · exact natDegree_mul_le.trans (add_le_add ((natDegree_theta_le p).trans hp) hq)

theorem X_pow_dvd_wronski4 {p q : K[X]} {n : ℕ} (h : X ^ n ∣ q) :
    X ^ n ∣ 4 * p * theta q - theta p * q :=
  dvd_sub (dvd_mul_of_dvd_right (X_pow_dvd_theta h) _) (dvd_mul_of_dvd_right h _)

/-- Top coefficient of `4 p θq - θp q`. -/
theorem coeff_wronski4_top {p q : K[X]} :
    (4 * p * theta q - theta p * q).coeff (p.natDegree + q.natDegree) =
      (4 * (q.natDegree : K) - p.natDegree) * p.leadingCoeff * q.leadingCoeff := by
  rw [coeff_sub, mul_assoc, coeff_ofNat_mul,
    coeff_mul_add_eq_of_natDegree_le le_rfl (natDegree_theta_le q),
    coeff_mul_add_eq_of_natDegree_le (natDegree_theta_le p) le_rfl, coeff_theta, coeff_theta]
  simp only [leadingCoeff]; ring

/-- If `X ^ n ∣ A ^ 4 - q Λ`, then `X ^ n ∣ q (4 Λ θA - θΛ A)`. -/
theorem X_pow_dvd_wronski_of_fourth {A Λ : K[X]} {q : K} {n : ℕ}
    (h : X ^ n ∣ A ^ 4 - C q * Λ) : X ^ n ∣ C q * (4 * Λ * theta A - theta Λ * A) := by
  obtain ⟨Z, hZ⟩ := h
  have hq : C q * Λ = A ^ 4 - X ^ n * Z := by linear_combination -hZ
  have hθ : theta (C q * Λ) = 4 * A ^ 3 * theta A - theta (X ^ n * Z) := by
    rw [hq, theta_sub]; congr 1
    rw [show A ^ 4 = A * (A * (A * A)) by ring, theta_mul, theta_mul, theta_mul]; ring
  have : C q * (4 * Λ * theta A - theta Λ * A) =
      A * theta (X ^ n * Z) - 4 * theta A * (X ^ n * Z) := by
    rw [theta_C_mul] at hθ
    linear_combination (4 * theta A) * hq - A * hθ
  rw [this]
  exact dvd_sub (dvd_mul_of_dvd_right (X_pow_dvd_theta (dvd_mul_right _ _)) _)
    (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)

/-- The coefficient identity of `(X ^ h + C a) ^ 3`. -/
theorem coeff_binom_cube {a : K} {h j : ℕ} (hj : j ≠ 0) (hj1 : j ≠ h) (hj2 : j ≠ 2 * h)
    (hj3 : j ≠ 3 * h) : ((X ^ h + C a) ^ 3).coeff j = 0 := by
  have : (X ^ h + C a) ^ 3 = X ^ (3 * h) + C (3 * a) * X ^ (2 * h) + C (3 * a ^ 2) * X ^ h + C (a ^ 3) := by
    simp only [map_mul, map_pow, map_ofNat]; ring
  rw [this, coeff_add, coeff_add, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    coeff_C]
  simp only [hj, hj1, hj2, hj3, ↓reduceIte, add_zero]

theorem coeff_binom2_cube {u v : K} {h j : ℕ} (hj : j ≠ 0) (hj1 : j ≠ h) (hj2 : j ≠ 2 * h)
    (hj3 : j ≠ 3 * h) : ((C u + C v * X ^ h) ^ 3).coeff j = 0 := by
  have : (C u + C v * X ^ h) ^ 3 = C (v ^ 3) * X ^ (3 * h) + C (3 * u * v ^ 2) * X ^ (2 * h) +
      C (3 * u ^ 2 * v) * X ^ h + C (u ^ 3) := by
    simp only [map_mul, map_pow, map_ofNat]; ring
  rw [this, coeff_add, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
    coeff_C_mul_X_pow, coeff_C]
  simp only [hj, hj1, hj2, hj3, ↓reduceIte, add_zero]

/-- The last step: `A = X ^ h + a0` is impossible. -/
theorem final_step {A B R : K[X]} {q0 a0 : K} {h D : ℕ} (hD1 : 1 ≤ D) (hDh : D < h)
    (hq0 : q0 ≠ 0) (hBd : B.natDegree ≤ h) (hAform : A = X ^ h + C a0)
    (hA3 : A ^ 3 = C q0 * B + X ^ (2 * h - D) * R)
    (hBR : B ^ 3 + R = C q0 * X ^ (2 * h) * A) : False := by
  have hBj : ∀ j, 0 < j → j < h → B.coeff j = 0 := by
    intro j h0 h1
    have := congrArg (fun p => p.coeff j) hA3
    simp only [coeff_add, coeff_C_mul, coeff_X_pow_mul', ite_eq_right (by omega : ¬ 2 * h - D ≤ j),
      add_zero] at this
    rw [hAform, coeff_binom_cube (by omega) (by omega) (by omega) (by omega)] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hq0
  have hBform : B = C (B.coeff 0) + C (B.coeff h) * X ^ h := by
    ext j
    rw [coeff_add, coeff_C, coeff_C_mul_X_pow]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [show (0 : ℕ) ≠ h by omega]
    · rcases lt_trichotomy j h with hjh | rfl | hjh
      · simp [hBj j hj hjh, show j ≠ 0 by omega, show j ≠ h by omega]
      · simp [show j ≠ 0 by omega]
      · rw [coeff_eq_zero_of_natDegree_lt (hBd.trans_lt hjh)]
        simp [show j ≠ 0 by omega, show j ≠ h by omega]
  have hA3top : (A ^ 3).coeff (3 * h) = 1 := by
    have : (X ^ h + C a0) ^ 3 = X ^ (3 * h) + C (3 * a0) * X ^ (2 * h) + C (3 * a0 ^ 2) * X ^ h +
        C (a0 ^ 3) := by
      simp only [map_mul, map_pow, map_ofNat]; ring
    rw [hAform, this, coeff_add, coeff_add, coeff_add, coeff_X_pow, coeff_C_mul_X_pow,
      coeff_C_mul_X_pow, coeff_C]
    simp only [show 3 * h ≠ 2 * h by omega, show 3 * h ≠ h by omega, show 3 * h ≠ 0 by omega,
      ↓reduceIte, add_zero]
  have h1 := congrArg (fun p => p.coeff (3 * h)) hA3
  simp only [coeff_add, coeff_C_mul, coeff_X_pow_mul', ite_eq_left (by omega : 2 * h - D ≤ 3 * h),
    coeff_eq_zero_of_natDegree_lt (hBd.trans_lt (by omega : h < 3 * h)), mul_zero, zero_add,
    hA3top, show 3 * h - (2 * h - D) = h + D by omega] at h1
  have h2 := congrArg (fun p => p.coeff (h + D)) hBR
  simp only [coeff_add, mul_assoc, coeff_C_mul, coeff_X_pow_mul',
    ite_eq_right (by omega : ¬ 2 * h ≤ h + D), mul_zero] at h2
  rw [hBform, coeff_binom2_cube (by omega) (by omega) (by omega) (by omega), zero_add, ← h1] at h2
  exact one_ne_zero h2

/-- **Theorem K0** (rukafe0x, result 29). Let `1 ≤ D`, `4D < h`, `e = 2h - D`, and let every positive
integer up to `4h` be nonzero in `K`. Then no `A` monic of degree `h`, `B` of degree `≤ h` with
`B(0) ≠ 0`, and `q0 ≠ 0` satisfy `A ^ 3 + X ^ e B ^ 3 = q0 (X ^ (e + 2h) A + B)`. -/
theorem theoremK0 {A B : K[X]} {q0 : K} {h D : ℕ} (hD1 : 1 ≤ D) (hDh : 4 * D < h)
    (hchar : ∀ n, 0 < n → n ≤ 4 * h → (n : K) ≠ 0)
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hq0 : q0 ≠ 0)
    (hident : A ^ 3 + X ^ (2 * h - D) * B ^ 3 = C q0 * (X ^ (2 * h - D + 2 * h) * A + B)) : False := by
  set e := 2 * h - D with he
  set R : K[X] := C q0 * X ^ (2 * h) * A - B ^ 3 with hR
  have hA3 : A ^ 3 = C q0 * B + X ^ e * R := by
    rw [hR]; rw [pow_add] at hident; linear_combination hident
  have hBR : B ^ 3 + R = C q0 * X ^ (2 * h) * A := by rw [hR]; ring
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast hchar 2 (by omega) (by omega)
  have h4 : (4 : K) ≠ 0 := by exact_mod_cast hchar 4 (by omega) (by omega)
  have hA0 : A.coeff 0 ≠ 0 := by
    intro h0
    have := congrArg (eval 0) hA3
    simp only [eval_pow, eval_add, eval_mul, eval_C, eval_X, ← coeff_zero_eq_eval_zero, h0,
      zero_pow (by omega : e ≠ 0), zero_pow (by norm_num : 3 ≠ 0), zero_mul, add_zero] at this
    exact mul_ne_zero hq0 (by rw [coeff_zero_eq_eval_zero]; exact hB0) this.symm
  have hAne : A ≠ 0 := hAm.ne_zero
  -- degrees of `R` and `B`
  have hRdeg : R.natDegree ≤ h + D := by
    by_cases hR0 : R = 0
    · rw [hR0, natDegree_zero]; omega
    have h1 : (X ^ e * R).natDegree ≤ 3 * h := by
      have : X ^ e * R = A ^ 3 - C q0 * B := by linear_combination -hA3
      rw [this]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · rw [natDegree_pow, hAd]
      · exact (natDegree_C_mul_le _ _).trans (by omega)
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hR0, natDegree_X_pow] at h1
    omega
  have hBdeg : B.natDegree = h := by
    have h1 : (C q0 * X ^ (2 * h) * A).natDegree = 3 * h := by
      rw [natDegree_mul (by simp [hq0]) hAne, natDegree_C_mul_X_pow _ _ hq0, hAd]; ring
    have h2' : (B ^ 3).natDegree = 3 * h := by
      have : B ^ 3 = C q0 * X ^ (2 * h) * A - R := by linear_combination hBR
      rw [this, natDegree_sub_eq_left_of_natDegree_lt (by rw [h1]; omega), h1]
    rw [natDegree_pow] at h2'; omega
  have hBne : B ≠ 0 := by rintro rfl; simp at hB0
  -- Lemma S
  have hθ : 3 * B ^ 2 * theta B + theta R = C q0 * X ^ (2 * h) * (C ((2 * h : ℕ) : K) * A + theta A) := by
    have e1 : theta (B ^ 3) = 3 * B ^ 2 * theta B := by
      rw [show B ^ 3 = B * (B * B) by ring, theta_mul, theta_mul]; ring
    have e2 : theta (C q0 * X ^ (2 * h) * A) =
        C q0 * X ^ (2 * h) * (C ((2 * h : ℕ) : K) * A + theta A) := by
      rw [mul_assoc, theta_C_mul, theta_mul, theta_X_pow]; ring
    have := congrArg theta hBR
    rw [theta_add, e1, e2] at this
    exact this
  set M : K[X] := 3 * A * theta B - B * theta A - C ((2 * h : ℕ) : K) * (A * B) with hM
  have hBM : B ^ 2 * M = (C ((2 * h : ℕ) : K) * A + theta A) * R - A * theta R := by
    rw [hM]; linear_combination A * hθ - (theta A + C ((2 * h : ℕ) : K) * A) * hBR
  have hMdeg : M.natDegree ≤ D := by
    by_cases hM0 : M = 0
    · rw [hM0, natDegree_zero]; omega
    have h1 : (B ^ 2 * M).natDegree ≤ 2 * h + D := by
      rw [hBM]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · have hX : (C ((2 * h : ℕ) : K) * A + theta A).natDegree ≤ h :=
          (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hAd.le)
            ((natDegree_theta_le A).trans hAd.le))
        exact natDegree_mul_le.trans ((add_le_add hX hRdeg).trans (by omega))
      · exact natDegree_mul_le.trans (add_le_add hAd.le ((natDegree_theta_le R).trans hRdeg)) |>.trans
          (by omega)
    rw [natDegree_mul (pow_ne_zero 2 hBne) hM0, natDegree_pow, hBdeg] at h1
    omega
  have hqB : C q0 * B = A ^ 3 - X ^ e * R := by linear_combination -hA3
  have hθqB : C q0 * theta B = 3 * A ^ 2 * theta A - theta (X ^ e * R) := by
    have e3 : theta (A ^ 3) = 3 * A ^ 2 * theta A := by
      rw [show A ^ 3 = A * (A * A) by ring, theta_mul, theta_mul]; ring
    rw [← theta_C_mul, hqB, theta_sub, e3]
  have hS : X ^ e ∣ M - 2 * theta (A * B) + C ((2 * h : ℕ) : K) * (A * B) := by
    have hid : C q0 * (M - 2 * theta (A * B) + C ((2 * h : ℕ) : K) * (A * B)) =
        3 * theta A * (X ^ e * R) - A * theta (X ^ e * R) := by
      rw [hM, theta_mul]; linear_combination A * hθqB - 3 * theta A * hqB
    have hd : X ^ e ∣ C q0 * (M - 2 * theta (A * B) + C ((2 * h : ℕ) : K) * (A * B)) := by
      rw [hid]
      exact dvd_sub (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
        (dvd_mul_of_dvd_right (X_pow_dvd_theta (dvd_mul_right _ _)) _)
    have hinv : (C q0⁻¹ * C q0 : K[X]) = 1 := by rw [← C_mul, inv_mul_cancel₀ hq0, C_1]
    have := dvd_mul_of_dvd_right hd (C q0⁻¹)
    rwa [← mul_assoc, hinv, one_mul] at this
  have hAB : ∀ j, D < j → j < e → j ≠ h → (A * B).coeff j = 0 := by
    intro j hj1 hj2 h3
    have hc := (X_pow_dvd_iff.mp hS) j hj2
    rw [coeff_add, coeff_sub, coeff_eq_zero_of_natDegree_lt (hMdeg.trans_lt hj1), coeff_ofNat_mul,
      coeff_theta, coeff_C_mul] at hc
    have hne : (2 * ((h : K) - j)) ≠ 0 := by
      refine mul_ne_zero h2 ?_
      rcases Nat.lt_or_gt_of_ne h3 with hl | hl
      · have := hchar (h - j) (by omega) (by omega)
        rw [Nat.cast_sub hl.le] at this; exact this
      · have := hchar (j - h) (by omega) (by omega)
        rw [Nat.cast_sub hl.le] at this; intro h0; exact this (by linear_combination -h0)
    have : (2 * ((h : K) - j)) * (A * B).coeff j = 0 := by push_cast at hc; linear_combination hc
    exact (mul_eq_zero.mp this).resolve_left hne
  -- `AB ≡ Λ = L0 + c X ^ h (mod X ^ e)`
  set L0 := lowPart (D + 1) (A * B) with hL0
  set c := (A * B).coeff h with hcdef
  set Λ : K[X] := L0 + C c * X ^ h with hΛ
  have hABΛ : X ^ e ∣ A * B - Λ := by
    rw [X_pow_dvd_iff]; intro i hi
    rw [coeff_sub, hΛ, coeff_add, hL0, coeff_lowPart, coeff_C_mul_X_pow]
    by_cases h1 : i < D + 1
    · rw [ite_eq_left h1, ite_eq_right (by omega : i ≠ h)]; ring
    · rw [ite_eq_right h1]
      by_cases h2 : i = h
      · rw [ite_eq_left h2, h2]; ring
      · rw [ite_eq_right h2, hAB i (by omega) hi h2]; ring
  have h4th : X ^ e ∣ A ^ 4 - C q0 * Λ := by
    have : A ^ 4 - C q0 * Λ = C q0 * (A * B - Λ) + X ^ e * (A * R) := by
      linear_combination A * hA3
    rw [this]; exact dvd_add (dvd_mul_of_dvd_right hABΛ _) (dvd_mul_right _ _)
  have hW : X ^ e ∣ 4 * Λ * theta A - theta Λ * A := by
    have hd := X_pow_dvd_wronski_of_fourth h4th
    have hinv : (C q0⁻¹ * C q0 : K[X]) = 1 := by rw [← C_mul, inv_mul_cancel₀ hq0, C_1]
    have := dvd_mul_of_dvd_right hd (C q0⁻¹)
    rwa [← mul_assoc, hinv, one_mul] at this
  have hL0_0 : L0.coeff 0 ≠ 0 := by
    rw [hL0, coeff_lowPart, ite_eq_left (by omega), coeff_zero_eq_eval_zero, eval_mul,
      ← coeff_zero_eq_eval_zero]
    exact mul_ne_zero hA0 hB0
  have hL0ne : L0 ≠ 0 := fun h0 => hL0_0 (by rw [h0, coeff_zero])
  have hL0deg : L0.natDegree ≤ D := natDegree_lowPart_le D _
  set P : K[X] := 4 * L0 * theta A - theta L0 * A with hP
  set G : K[X] := 4 * theta A - C (h : K) * A with hG
  have hWsplit : 4 * Λ * theta A - theta Λ * A = P + C c * X ^ h * G := by
    rw [hΛ, theta_add, theta_C_mul, theta_X_pow, hP, hG]; ring
  have hPdeg : P.natDegree ≤ D + h := natDegree_wronski4_le hL0deg hAd.le
  by_cases hc : c = 0
  · -- `c = 0`: `P = 0`, but its top coefficient is not
    have hP0 : P = 0 := by
      have hdv : X ^ e ∣ P := by
        have := hW; rw [hWsplit, hc, map_zero, zero_mul, zero_mul, add_zero] at this; exact this
      exact eq_zero_of_dvd_of_natDegree_lt hdv (by rw [natDegree_X_pow]; omega)
    have htop := coeff_wronski4_top (p := L0) (q := A)
    rw [← hP, hP0, coeff_zero, hAd, hAm.leadingCoeff, mul_one] at htop
    have hm : (4 * (h : K) - L0.natDegree) ≠ 0 := by
      have := hchar (4 * h - L0.natDegree) (by omega) (by omega)
      rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
    exact mul_ne_zero hm (mt leadingCoeff_eq_zero.mp hL0ne) htop.symm
  -- `c ≠ 0`
  have hWdvd := hW
  rw [hWsplit] at hWdvd
  have hcX : ∀ i, (C c * X ^ h * G).coeff i = if h ≤ i then c * G.coeff (i - h) else 0 := by
    intro i; rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']; split_ifs <;> simp
  have hPh : X ^ h ∣ P := by
    rw [X_pow_dvd_iff]; intro i hi
    have := (X_pow_dvd_iff.mp hWdvd) i (by omega)
    rw [coeff_add, hcX, ite_eq_right (by omega : ¬ h ≤ i), add_zero] at this; exact this
  have hGj : ∀ j, D < j → j < h - D → G.coeff j = 0 := by
    intro j hj1 hj2
    have := (X_pow_dvd_iff.mp hWdvd) (h + j) (by omega)
    rw [coeff_add, hcX, ite_eq_left (by omega : h ≤ h + j),
      coeff_eq_zero_of_natDegree_lt (hPdeg.trans_lt (by omega)), zero_add,
      show h + j - h = j by omega] at this
    exact (mul_eq_zero.mp this).resolve_left hc
  have hAj : ∀ j, D < j → j < h - D → h < 4 * j → A.coeff j = 0 := by
    intro j hj1 hj2 hj3
    have := hGj j hj1 hj2
    rw [hG, coeff_sub, coeff_ofNat_mul, coeff_theta, coeff_C_mul] at this
    have hm : ((4 * j - h : ℕ) : K) ≠ 0 := hchar _ (by omega) (by omega)
    rw [Nat.cast_sub (by omega)] at hm; push_cast at hm
    have : ((4 : K) * j - h) * A.coeff j = 0 := by linear_combination this
    exact (mul_eq_zero.mp this).resolve_left hm
  -- the truncation `a` of `A` below `h - D`
  set a := lowPart (h - D) A with ha
  have hadeg : a.natDegree ≤ h / 4 := by
    rw [natDegree_le_iff_coeff_eq_zero]; intro i hi
    rw [ha, coeff_lowPart]; split_ifs with h1
    · exact hAj i (by omega) h1 (by omega)
    · rfl
  have hAa : X ^ (h - D) ∣ A - a := X_pow_dvd_sub_lowPart _ _
  have hE0 : 4 * L0 * theta a - theta L0 * a = 0 := by
    have hd : X ^ (h - D) ∣ 4 * L0 * theta a - theta L0 * a := by
      have : 4 * L0 * theta a - theta L0 * a =
          P - (4 * L0 * theta (A - a) - theta L0 * (A - a)) := by rw [hP, theta_sub]; ring
      rw [this]
      exact dvd_sub ((pow_dvd_pow X (by omega)).trans hPh) (X_pow_dvd_wronski4 hAa)
    refine eq_zero_of_dvd_of_natDegree_lt hd ?_
    rw [natDegree_X_pow]
    exact (natDegree_wronski4_le hL0deg hadeg).trans_lt (by omega)
  have ha0 : a.coeff 0 = A.coeff 0 := by rw [ha, coeff_lowPart, ite_eq_left (by omega)]
  have hane : a ≠ 0 := fun h0 => hA0 (by rw [← ha0, h0, coeff_zero])
  have h4a : 4 * a.natDegree = L0.natDegree := by
    have htop := coeff_wronski4_top (p := L0) (q := a)
    rw [hE0, coeff_zero] at htop
    by_contra hne
    have hm : (4 * (a.natDegree : K) - L0.natDegree) ≠ 0 := by
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · have := hchar (L0.natDegree - 4 * a.natDegree) (by omega) (by omega)
        rw [Nat.cast_sub hl.le] at this; push_cast at this
        intro h0; exact this (by linear_combination -h0)
      · have := hchar (4 * a.natDegree - L0.natDegree) (by omega) (by omega)
        rw [Nat.cast_sub hl.le] at this; push_cast at this; exact this
    exact mul_ne_zero (mul_ne_zero hm (mt leadingCoeff_eq_zero.mp hL0ne))
      (mt leadingCoeff_eq_zero.mp hane) htop.symm
  obtain ⟨Ah, hAh⟩ := hAa
  have hA_eq : A = a + X ^ (h - D) * Ah := by linear_combination hAh
  have hAhdeg : Ah.natDegree ≤ D := by
    by_cases hAh0 : Ah = 0
    · rw [hAh0, natDegree_zero]; omega
    have h1 : (A - a).natDegree ≤ h :=
      (natDegree_sub_le _ _).trans (max_le hAd.le (hadeg.trans (by omega)))
    rw [hAh, natDegree_mul (pow_ne_zero _ X_ne_zero) hAh0, natDegree_X_pow] at h1
    omega
  obtain ⟨Z, hZ⟩ := h4th
  have hph : (X : K[X]) ^ h = X ^ (h - D) * X ^ D := by rw [← pow_add]; congr 1; omega
  have hpe : (X : K[X]) ^ e = X ^ (h - D) * X ^ h := by rw [← pow_add]; congr 1; omega
  have hZ' : (a + X ^ (h - D) * Ah) ^ 4 - C q0 * (L0 + C c * X ^ h) = X ^ e * Z := by
    rw [← hA_eq, ← hΛ]; exact hZ
  have key : a ^ 4 - C q0 * L0 = X ^ (h - D) * (X ^ h * Z - Ah * (4 * a ^ 3 +
      6 * a ^ 2 * (X ^ (h - D) * Ah) + 4 * a * (X ^ (h - D) * Ah) ^ 2 + (X ^ (h - D) * Ah) ^ 3) +
      C q0 * C c * X ^ D) := by
    linear_combination hZ' + C q0 * C c * hph + Z * hpe
  have ha4 : a ^ 4 = C q0 * L0 := by
    have hd : X ^ (h - D) ∣ a ^ 4 - C q0 * L0 := ⟨_, key⟩
    have h0 := eq_zero_of_dvd_of_natDegree_lt hd (by
      rw [natDegree_X_pow]
      refine (natDegree_sub_le _ _).trans_lt (max_lt ?_ ?_)
      · exact (natDegree_pow_le).trans_lt (by omega)
      · exact (natDegree_C_mul_le _ _).trans_lt (by omega))
    linear_combination h0
  have inner : X ^ h * Z - Ah * (4 * a ^ 3 + 6 * a ^ 2 * (X ^ (h - D) * Ah) +
      4 * a * (X ^ (h - D) * Ah) ^ 2 + (X ^ (h - D) * Ah) ^ 3) + C q0 * C c * X ^ D = 0 := by
    have : X ^ (h - D) * (X ^ h * Z - Ah * (4 * a ^ 3 + 6 * a ^ 2 * (X ^ (h - D) * Ah) +
        4 * a * (X ^ (h - D) * Ah) ^ 2 + (X ^ (h - D) * Ah) ^ 3) + C q0 * C c * X ^ D) = 0 := by
      rw [← key, ha4, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ X_ne_zero)
  have hlin : 4 * a ^ 3 * Ah - C q0 * C c * X ^ D = 0 := by
    have hd : X ^ (h - D) ∣ 4 * a ^ 3 * Ah - C q0 * C c * X ^ D :=
      ⟨X ^ D * Z - Ah * (6 * a ^ 2 * Ah + 4 * a * X ^ (h - D) * Ah ^ 2 +
        X ^ (h - D) * X ^ (h - D) * Ah ^ 3), by linear_combination -inner + Z * hph⟩
    refine eq_zero_of_dvd_of_natDegree_lt hd ?_
    rw [natDegree_X_pow]
    refine (natDegree_sub_le _ _).trans_lt (max_lt ?_ ?_)
    · refine natDegree_mul_le.trans_lt ?_
      have : (4 * a ^ 3).natDegree ≤ 3 * a.natDegree :=
        natDegree_mul_le.trans (by simp)
      omega
    · rw [← C_mul]; exact (natDegree_C_mul_X_pow_le _ _).trans_lt (by omega)
  -- `a` is constant
  have h4Ah : a ^ 3 * (4 * Ah) = C q0 * C c * X ^ D := by linear_combination hlin
  have hcopX : IsCoprime (X : K[X]) a :=
    (irreducible_X.coprime_iff_not_dvd).mpr (by rw [X_dvd_iff, ha0]; exact hA0)
  have hqc : C q0 * C c * X ^ D ≠ 0 := by
    rw [← C_mul]; exact mul_ne_zero (by simp [hq0, hc]) (pow_ne_zero _ X_ne_zero)
  have hne4 : 4 * Ah ≠ 0 := by intro h0; rw [h0, mul_zero] at h4Ah; exact hqc h4Ah.symm
  have hdv : X ^ D ∣ 4 * Ah :=
    (hcopX.pow (m := D) (n := 3)).dvd_of_dvd_mul_left (by rw [h4Ah]; exact dvd_mul_left _ _)
  have hdeg4 : D ≤ (4 * Ah).natDegree := by
    have := natDegree_le_of_dvd hdv hne4; rwa [natDegree_X_pow] at this
  have hda0 : a.natDegree = 0 := by
    have := congrArg natDegree h4Ah
    rw [natDegree_mul (pow_ne_zero 3 hane) hne4, natDegree_pow, ← C_mul,
      natDegree_C_mul_X_pow _ _ (mul_ne_zero hq0 hc)] at this
    omega
  have haC : a = C (A.coeff 0) := by rw [eq_C_of_natDegree_eq_zero hda0, ha0]
  have ha3 : a ^ 3 = C (A.coeff 0 ^ 3) := by rw [haC, C_pow]
  have hAhC : Ah = C (Ah.coeff D) * X ^ D := by
    ext i
    rw [coeff_C_mul_X_pow]
    split_ifs with hi
    · rw [hi]
    · have := congrArg (fun p => p.coeff i) h4Ah
      rw [ha3, coeff_C_mul, coeff_ofNat_mul, ← C_mul, coeff_C_mul_X_pow, ite_eq_right hi] at this
      exact (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hA0))).resolve_left h4
  generalize hκ : Ah.coeff D = κ at hAhC
  have h1 : A = C (A.coeff 0) + C κ * X ^ h := by
    conv_lhs => rw [hA_eq]
    rw [haC, hAhC, hph]; ring
  have h2 : A.coeff h = 1 := by rw [← hAd]; exact hAm
  have h3 : κ = 1 := by
    have h2' := h2
    rw [h1, coeff_add, coeff_C, coeff_C_mul_X_pow, ite_eq_left rfl, ite_eq_right (by omega : h ≠ 0),
      zero_add] at h2'
    exact h2'
  have hAform : A = X ^ h + C (A.coeff 0) := by
    conv_lhs => rw [h1]
    rw [h3, map_one, one_mul]; ring
  exact final_step hD1 (by omega) hq0 hBd hAform hA3 hBR


/-- **Theorem K0**, with result 29's characteristic hypothesis: characteristic `0` or above `4h`. -/
theorem theoremK0_ringChar {A B : K[X]} {q0 : K} {h D : ℕ} (hD1 : 1 ≤ D) (hDh : 4 * D < h)
    (hchar : ringChar K = 0 ∨ 4 * h < ringChar K)
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hq0 : q0 ≠ 0)
    (hident : A ^ 3 + X ^ (2 * h - D) * B ^ 3 = C q0 * (X ^ (2 * h - D + 2 * h) * A + B)) : False :=
  theoremK0 hD1 hDh (fun _ h0 h1 => natCast_ne_zero_of_char hchar h0 h1) hAm hAd hBd hB0 hq0 hident

end TheoremK0
