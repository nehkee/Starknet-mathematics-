import MCAChallenge
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Lemma CG (rukafe0x, result 27, Theorem CG; row M-1002), in Lean

Target `LEMMA` (tier 3, `problem-3a-upper`). The house named this lemma in bp1_34c30b51 as the Lean step that
removes every boundary cell `4h = N` from the single-monomial residual of the InteriorThree reduction.

Main statements (any field `K` of characteristic `0` or above `4h + c - 2`, `e = 2h + c`, `1 ≤ c ≤ h - 1`,
`S` an `h`-subset of the `e`-th roots of unity):
* `LemmaCG.lemmaCG_A`: `(∏_{s ∈ S} (X - s)) ^ 3` is nonzero in some degree `d`, `h + c < d < e`
  (the gap (Ga) of result 12, the form result 27 applies to the boundary cells);
* `LemmaCG.lemmaCG_F`: `(∏_{s ∈ S} (X - s)) ^ 3` is nonzero in some degree `d`, `h - c < d < 2h - c`
  (the form `F^3 ≠ T + X^(h+g) H`, `deg T ≤ g = h - c`, of result 27).

Route (polynomials only; no power-series square roots):
1. `star_of_gap`: the ODE `3TF' - T'F = K X^(N-1)`, `K ≠ 0`, and Bezout at the roots give
   `X^e ∣ 1 + M F^2 + κ X^(2c) F^4` with `deg M ≤ c`, `κ ≠ 0`.
2. `endgame`: with `k^2 = κ`, `A = -M + 2k X^c`, `B = -M - 2k X^c`, `G = F⁻¹ mod X^(e+c)`, the polynomials
   `α = (1 + k X^c F^2) G` and `β = (1 - k X^c F^2) G` satisfy `α^2 ≡ A`, `β^2 ≡ B (mod X^e)` and
   `α - β ≡ 2k X^c F (mod X^(e+c))`. The θ-recurrences (`θ = X d/dX`), their difference to order `e + c`
   and the `descent` make `α`, `β` congruent mod `X^e` to polynomials of degree `≤ c/2`; then
   `X^e ∣ 2k X^c F`, so `F(0) = 0`, a contradiction.
3. `lemmaCG_F` passes to the algebraic closure for `k`; `lemmaCG_A` follows by reversal (`S ↦ S⁻¹`).
-/

namespace LemmaCG

open Polynomial

variable {K : Type*} [Field K]

/-- The Euler operator `θ = X · d/dX`. -/
noncomputable def theta (p : K[X]) : K[X] := X * derivative p

theorem coeff_theta (p : K[X]) (i : ℕ) : (theta p).coeff i = (i : K) * p.coeff i := by
  unfold theta
  rcases i with _ | i
  · simp
  · rw [coeff_X_mul, coeff_derivative]; push_cast; ring

theorem theta_mul (p q : K[X]) : theta (p * q) = theta p * q + p * theta q := by
  unfold theta; rw [derivative_mul]; ring

theorem theta_sub (p q : K[X]) : theta (p - q) = theta p - theta q := by
  unfold theta; rw [derivative_sub]; ring

theorem theta_add (p q : K[X]) : theta (p + q) = theta p + theta q := by
  unfold theta; rw [derivative_add]; ring

theorem theta_C_mul (a : K) (p : K[X]) : theta (C a * p) = C a * theta p := by
  unfold theta; rw [derivative_C_mul]; ring

theorem theta_X_pow (n : ℕ) : theta (X ^ n : K[X]) = C (n : K) * X ^ n := by
  ext i
  rw [coeff_theta, coeff_C_mul, coeff_X_pow]
  split_ifs with h <;> simp [h]

theorem natDegree_theta_le (p : K[X]) : (theta p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_theta, coeff_eq_zero_of_natDegree_lt hi, mul_zero]

theorem X_pow_dvd_iff' {n : ℕ} {p : K[X]} : X ^ n ∣ p ↔ ∀ i < n, p.coeff i = 0 :=
  X_pow_dvd_iff

theorem X_pow_dvd_theta {n : ℕ} {p : K[X]} (h : X ^ n ∣ p) : X ^ n ∣ theta p := by
  rw [X_pow_dvd_iff] at h ⊢
  intro i hi; rw [coeff_theta, h i hi, mul_zero]

/-- The part of `p` in degrees `< n`. -/
noncomputable def lowPart (n : ℕ) (p : K[X]) : K[X] :=
  ∑ i ∈ Finset.range n, C (p.coeff i) * X ^ i

theorem coeff_lowPart (n : ℕ) (p : K[X]) (i : ℕ) :
    (lowPart n p).coeff i = if i < n then p.coeff i else 0 := by
  unfold lowPart
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hi; exact absurd (Finset.mem_range.mpr h) hi
  · apply Finset.sum_eq_zero
    intro b hb
    have : i ≠ b := fun e => h (e ▸ Finset.mem_range.mp hb)
    simp [this]

theorem natDegree_lowPart_le (n : ℕ) (p : K[X]) : (lowPart (n + 1) p).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_lowPart, ite_eq_right (by omega : ¬ i < n + 1)]

theorem X_pow_dvd_sub_lowPart (n : ℕ) (p : K[X]) : X ^ n ∣ p - lowPart n p := by
  rw [X_pow_dvd_iff]
  intro i hi
  rw [coeff_sub, coeff_lowPart, ite_eq_left hi, sub_self]

/-- From a natural-number bound on the characteristic: every positive `n ≤ B` is nonzero in `K`. -/
theorem natCast_ne_zero_of_char {B : ℕ} (hchar : ringChar K = 0 ∨ B < ringChar K) {n : ℕ}
    (hn0 : 0 < n) (hnB : n ≤ B) : (n : K) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff K (ringChar K)] at h
  rcases hchar with h0 | hB
  · rw [h0, zero_dvd_iff] at h; omega
  · have := Nat.le_of_dvd hn0 h; omega

/-- The descent of result 27: if `2 A θα - θA · α ≡ 0 mod X ^ e` and `α` has zero coefficients on
`[W0, e)`, then every coefficient `α_M` with `deg A < 2 M < 2 e` vanishes. The row `M + deg A` of the
recurrence reads `(2 M - deg A) · lead A · α_M = 0`. -/
theorem descent {A α : K[X]} {e W0 B : ℕ} (hchar : ∀ n, 0 < n → n ≤ B → (n : K) ≠ 0)
    (hA : A ≠ 0) (hW0e : W0 + A.natDegree ≤ e) (hB : 2 * W0 ≤ B + 2)
    (hdiv : X ^ e ∣ 2 * A * theta α - theta A * α)
    (hW : ∀ i, W0 ≤ i → i < e → α.coeff i = 0) :
    ∀ M, A.natDegree < 2 * M → M < e → α.coeff M = 0 := by
  intro M
  induction hm : e - M using Nat.strong_induction_on generalizing M with
  | _ t ih =>
  intro hdM hMe
  by_cases hMW : W0 ≤ M
  · exact hW M hMW hMe
  replace hMW : M < W0 := by omega
  set d := A.natDegree with hd
  set P := lowPart (M + 1) α with hP
  have hgap : X ^ (M + d + 1) ∣ α - P := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [coeff_sub, hP, coeff_lowPart]
    split_ifs with h
    · ring
    · rw [sub_zero]
      exact ih (e - i) (by omega) i rfl (by omega) (by omega)
  have hdivP : X ^ (M + d + 1) ∣ 2 * A * theta P - theta A * P := by
    have h1 : X ^ (M + d + 1) ∣ 2 * A * theta α - theta A * α :=
      (pow_dvd_pow X (by omega)).trans hdiv
    have h2 : X ^ (M + d + 1) ∣ 2 * A * theta (α - P) - theta A * (α - P) :=
      dvd_sub (dvd_mul_of_dvd_right (X_pow_dvd_theta hgap) _) (dvd_mul_of_dvd_right hgap _)
    have : 2 * A * theta P - theta A * P =
        (2 * A * theta α - theta A * α) - (2 * A * theta (α - P) - theta A * (α - P)) := by
      rw [theta_sub]; ring
    rw [this]; exact dvd_sub h1 h2
  have hcoef := (X_pow_dvd_iff.mp hdivP) (M + d) (by omega)
  have hPdeg : P.natDegree ≤ M := natDegree_lowPart_le M α
  have hPM : P.coeff M = α.coeff M := by rw [hP, coeff_lowPart, ite_eq_left (by omega : M < M + 1)]
  rw [coeff_sub, mul_assoc, coeff_ofNat_mul, show M + d = d + M by ring,
    coeff_mul_add_eq_of_natDegree_le (le_of_eq hd.symm) ((natDegree_theta_le P).trans hPdeg),
    coeff_mul_add_eq_of_natDegree_le ((natDegree_theta_le A).trans (le_of_eq hd.symm)) hPdeg,
    coeff_theta, coeff_theta, hPM] at hcoef
  have hlead : A.coeff d ≠ 0 := by rw [hd]; exact mt leadingCoeff_eq_zero.mp hA
  have hmult : ((2 * M - d : ℕ) : K) ≠ 0 := hchar _ (by omega) (by omega)
  have : ((2 * M - d : ℕ) : K) * A.coeff d * α.coeff M = 0 := by
    rw [Nat.cast_sub (by omega)]; push_cast; linear_combination hcoef
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (mul_ne_zero hmult hlead)
  · exact h

theorem natDegree_wronski_le {p q : K[X]} {a b : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (2 * p * theta q - theta p * q).natDegree ≤ a + b := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans (add_le_add ?_ ((natDegree_theta_le q).trans hq))
    refine natDegree_mul_le.trans ?_
    simpa using hp
  · exact natDegree_mul_le.trans (add_le_add ((natDegree_theta_le p).trans hp) hq)

theorem X_pow_dvd_wronski {p q : K[X]} {n : ℕ} (h : X ^ n ∣ q) :
    X ^ n ∣ 2 * p * theta q - theta p * q :=
  dvd_sub (dvd_mul_of_dvd_right (X_pow_dvd_theta h) _) (dvd_mul_of_dvd_right h _)

/-- If `α ^ 2 ≡ A (mod X ^ n)`, then `2 A θα - θA α ≡ 0 (mod X ^ n)`. -/
theorem recur_dvd {A α : K[X]} {n : ℕ} (h : X ^ n ∣ α ^ 2 - A) :
    X ^ n ∣ 2 * A * theta α - theta A * α := by
  have key : 2 * A * theta α - theta A * α =
      α * theta (α ^ 2 - A) - 2 * (α ^ 2 - A) * theta α := by
    rw [theta_sub, pow_two, theta_mul]; ring
  rw [key]
  exact dvd_sub (dvd_mul_of_dvd_right (X_pow_dvd_theta h) _)
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)

theorem natDegree_A_le {Mp : K[X]} {c : ℕ} (s : K) (hM : Mp.natDegree ≤ c) :
    (-Mp + C s * X ^ c).natDegree ≤ c :=
  (natDegree_add_le _ _).trans (max_le (by rwa [natDegree_neg]) (natDegree_C_mul_X_pow_le _ _))

/-- The endgame. If `F(0) ≠ 0`, `deg F ≤ h`, `deg M ≤ c`, `k ≠ 0` and
`X ^ e ∣ 1 + M F ^ 2 + k ^ 2 X ^ (2c) F ^ 4` with `e = 2h + c`, `1 ≤ c < h`, and every positive integer
up to `4h + c - 2` is nonzero in `K`, we reach a contradiction. With `A = -M + 2k X^c`,
`B = -M - 2k X^c`, `a = 1 + k X^c F^2`, `b = 1 - k X^c F^2` and `G = F⁻¹ mod X^(e+c)`, the polynomials
`α = aG`, `β = bG` satisfy `α² ≡ A`, `β² ≡ B (mod X^e)` and `α - β ≡ 2k X^c F (mod X^(e+c))`. -/
theorem endgame {F Mp : K[X]} {h c : ℕ} {k : K} (hc : 1 ≤ c) (hch : c < h)
    (hchar : ∀ n, 0 < n → n ≤ 4 * h + c - 2 → (n : K) ≠ 0)
    (hk : k ≠ 0) (hF0 : F.coeff 0 ≠ 0) (hFdeg : F.natDegree ≤ h) (hMdeg : Mp.natDegree ≤ c)
    (hstar : X ^ (2 * h + c) ∣ 1 + Mp * F ^ 2 + C (k ^ 2) * X ^ (2 * c) * F ^ 4) : False := by
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast hchar 2 (by omega) (by omega)
  -- an inverse of `F` modulo `X ^ (e + c)`
  have hXF : ¬ X ∣ F := by rw [X_dvd_iff]; exact hF0
  have hcop : IsCoprime F (X ^ (2 * h + c + c)) :=
    ((irreducible_X.coprime_iff_not_dvd).mpr hXF).symm.pow_right
  obtain ⟨G, v, hGv⟩ := hcop
  have hGF : G * F = 1 - v * X ^ (2 * h + c + c) := by linear_combination hGv
  obtain ⟨W₀, hW₀⟩ := hstar
  set A : K[X] := -Mp + C (2 * k) * X ^ c with hA
  set B : K[X] := -Mp + C (-(2 * k)) * X ^ c with hB
  set α : K[X] := (1 + C k * X ^ c * F ^ 2) * G with hα
  set β : K[X] := (1 - C k * X ^ c * F ^ 2) * G with hβ
  set γ : K[X] := α - β with hγ
  set r : K[X] := -(C (2 * k) * X ^ c * F * v) with hr
  -- exact forms
  have hδα : α ^ 2 - A = X ^ (2 * h + c) *
      (A * (-(2 * v * X ^ c) + v ^ 2 * X ^ c * X ^ (2 * h + c + c)) + W₀ * G ^ 2) := by
    rw [hα, hA]
    simp only [map_mul, map_pow, map_ofNat] at hW₀ ⊢
    linear_combination G ^ 2 * hW₀ + (-Mp + 2 * C k * X ^ c) * (G * F + 1 - v * X ^ (2 * h + c + c)) * hGF
  have hδβ : β ^ 2 - B = X ^ (2 * h + c) *
      (B * (-(2 * v * X ^ c) + v ^ 2 * X ^ c * X ^ (2 * h + c + c)) + W₀ * G ^ 2) := by
    rw [hβ, hB]
    simp only [map_mul, map_neg, map_pow, map_ofNat] at hW₀ ⊢
    linear_combination G ^ 2 * hW₀ + (-Mp - 2 * C k * X ^ c) * (G * F + 1 - v * X ^ (2 * h + c + c)) * hGF
  have hγ' : α - β = C (2 * k) * X ^ c * F + X ^ (2 * h + c + c) * r := by
    rw [hα, hβ, hr]
    simp only [map_mul, map_ofNat]
    linear_combination (2 * C k * X ^ c * F) * hGF
  have hpow : (X : K[X]) ^ (2 * h + c + c) = X ^ (2 * h + c) * X ^ c := pow_add _ _ _
  have hXcγ : X ^ c ∣ α - β := ⟨C (2 * k) * F + X ^ (2 * h + c) * r, by rw [hγ', hpow]; ring⟩
  have hdivα : X ^ (2 * h + c) ∣ α ^ 2 - A := ⟨_, hδα⟩
  have hdivβ : X ^ (2 * h + c) ∣ β ^ 2 - B := ⟨_, hδβ⟩
  have hRα := recur_dvd hdivα
  have hRβ := recur_dvd hdivβ
  -- the difference of the two recurrences holds to order `e + c`
  have hAB : A = B + C (4 * k) * X ^ c := by
    rw [hA, hB]; simp only [map_mul, map_neg, map_ofNat]; ring
  have hθA : theta A = theta B + C (4 * k) * (C (c : K) * X ^ c) := by
    rw [hAB, theta_add, theta_C_mul, theta_X_pow]
  have hρ : X ^ (2 * h + c + c) ∣ (α ^ 2 - A) - (β ^ 2 - B) := by
    refine ⟨(A - B) * (-(2 * v) + v ^ 2 * X ^ (2 * h + c + c)), ?_⟩
    rw [hδα, hδβ, hAB, hpow]; ring
  have hD : X ^ (2 * h + c + c) ∣
      (2 * A * theta α - theta A * α) - (2 * B * theta β - theta B * β) := by
    have key : (2 * A * theta α - theta A * α) - (2 * B * theta β - theta B * β) =
        ((α - β) * theta (β ^ 2 - B) - 2 * (β ^ 2 - B) * theta (α - β)) +
        (α * theta ((α ^ 2 - A) - (β ^ 2 - B)) - 2 * ((α ^ 2 - A) - (β ^ 2 - B)) * theta α) := by
      simp only [theta_sub, theta_mul, pow_two]; ring
    rw [key]
    refine dvd_add (dvd_sub ?_ ?_) (dvd_sub (dvd_mul_of_dvd_right (X_pow_dvd_theta hρ) _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hρ _) _))
    · rw [hpow, mul_comm (X ^ (2 * h + c))]
      exact mul_dvd_mul hXcγ (X_pow_dvd_theta hdivβ)
    · rw [hpow, mul_comm (2 * (β ^ 2 - B)), mul_comm (X ^ (2 * h + c))]
      exact mul_dvd_mul (X_pow_dvd_theta hXcγ) (dvd_mul_of_dvd_right hdivβ _)
  have hDeq : (2 * A * theta α - theta A * α) - (2 * B * theta β - theta B * β) =
      ((2 * A * theta (C (2 * k) * X ^ c * F) - theta A * (C (2 * k) * X ^ c * F)) +
        (2 * A * theta (X ^ (2 * h + c + c) * r) - theta A * (X ^ (2 * h + c + c) * r))) +
      C (4 * k) * (2 * theta β - C (c : K) * β) * X ^ c := by
    have hθ : theta α = theta β + theta (C (2 * k) * X ^ c * F) + theta (X ^ (2 * h + c + c) * r) := by
      rw [← theta_add, ← theta_add]; congr 1; linear_combination hγ'
    have hα' : α = β + C (2 * k) * X ^ c * F + X ^ (2 * h + c + c) * r := by
      linear_combination hγ'
    rw [hθ]
    linear_combination (2 * theta β) * hAB - β * hθA + (-(theta A)) * hα'
  have hYdeg : (C (2 * k) * X ^ c * F).natDegree ≤ c + h :=
    natDegree_mul_le.trans (add_le_add (natDegree_C_mul_X_pow_le _ _) hFdeg)
  have hAdeg : A.natDegree ≤ c := natDegree_A_le _ hMdeg
  have hBdeg : B.natDegree ≤ c := natDegree_A_le _ hMdeg
  have hwinβ : ∀ M, h + c + 1 ≤ M → M < 2 * h + c → β.coeff M = 0 := by
    intro M hM1 hM2
    have h0 := (X_pow_dvd_iff.mp hD) (M + c) (by omega)
    rw [hDeq, coeff_add, coeff_add, coeff_mul_X_pow,
      coeff_eq_zero_of_natDegree_lt ((natDegree_wronski_le hAdeg hYdeg).trans_lt (by omega)),
      (X_pow_dvd_iff.mp (X_pow_dvd_wronski (p := A) (dvd_mul_right _ r))) (M + c) (by omega),
      coeff_C_mul, coeff_sub, coeff_ofNat_mul, coeff_theta, coeff_C_mul] at h0
    have hm : ((2 * M - c : ℕ) : K) ≠ 0 := hchar _ (by omega) (by omega)
    have h4 : (4 : K) ≠ 0 := by exact_mod_cast hchar 4 (by omega) (by omega)
    have : (4 * k * ((2 * M - c : ℕ) : K)) * β.coeff M = 0 := by
      rw [Nat.cast_sub (by omega)]; push_cast; linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero (mul_ne_zero h4 hk) hm)
    · exact h
  have hwinα : ∀ M, h + c + 1 ≤ M → M < 2 * h + c → α.coeff M = 0 := by
    intro M hM1 hM2
    have hγM : (α - β).coeff M = 0 := by
      rw [hγ', coeff_add, coeff_eq_zero_of_natDegree_lt (hYdeg.trans_lt (by omega)),
        (X_pow_dvd_iff.mp (dvd_mul_right (X ^ (2 * h + c + c)) r)) M (by omega), add_zero]
    rw [coeff_sub, hwinβ M hM1 hM2, sub_zero] at hγM
    exact hγM
  -- constant terms
  have hn0 : (2 * h + c + c) ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  have hαF : α * F = (1 + C k * X ^ c * F ^ 2) * (1 - v * X ^ (2 * h + c + c)) := by
    rw [hα, mul_assoc, hGF]
  have hβF : β * F = (1 - C k * X ^ c * F ^ 2) * (1 - v * X ^ (2 * h + c + c)) := by
    rw [hβ, mul_assoc, hGF]
  have hα0 : α.coeff 0 ≠ 0 := by
    intro h0
    have := congrArg (eval 0) hαF
    simp [eval_mul, ← coeff_zero_eq_eval_zero, h0, zero_pow hc0, zero_pow hn0] at this
  have hβ0 : β.coeff 0 ≠ 0 := by
    intro h0
    have := congrArg (eval 0) hβF
    simp [eval_mul, ← coeff_zero_eq_eval_zero, h0, zero_pow hc0, zero_pow hn0] at this
  have hA0 : A ≠ 0 := by
    intro hA0
    have := (X_pow_dvd_iff.mp hdivα) 0 (by omega)
    rw [coeff_sub, hA0, coeff_zero, sub_zero, coeff_zero_eq_eval_zero, eval_pow,
      ← coeff_zero_eq_eval_zero] at this
    exact hα0 (pow_eq_zero_iff (by norm_num) |>.mp this)
  have hB0 : B ≠ 0 := by
    intro hB0
    have := (X_pow_dvd_iff.mp hdivβ) 0 (by omega)
    rw [coeff_sub, hB0, coeff_zero, sub_zero, coeff_zero_eq_eval_zero, eval_pow,
      ← coeff_zero_eq_eval_zero] at this
    exact hβ0 (pow_eq_zero_iff (by norm_num) |>.mp this)
  -- the descents
  have hdα := descent (B := 4 * h + c - 2) (W0 := h + c + 1) hchar hA0 (by omega) (by omega) hRα hwinα
  have hdβ := descent (B := 4 * h + c - 2) (W0 := h + c + 1) hchar hB0 (by omega) (by omega) hRβ hwinβ
  set L := lowPart (A.natDegree / 2 + 1) α with hL
  set L' := lowPart (B.natDegree / 2 + 1) β with hL'
  have hXL : X ^ (2 * h + c) ∣ α - L := by
    rw [X_pow_dvd_iff]; intro i hi
    rw [coeff_sub, hL, coeff_lowPart]
    split_ifs with hi'
    · ring
    · rw [sub_zero]; exact hdα i (by omega) hi
  have hXL' : X ^ (2 * h + c) ∣ β - L' := by
    rw [X_pow_dvd_iff]; intro i hi
    rw [coeff_sub, hL', coeff_lowPart]
    split_ifs with hi'
    · ring
    · rw [sub_zero]; exact hdβ i (by omega) hi
  have hXe_c : (X : K[X]) ^ c ∣ X ^ (2 * h + c) := pow_dvd_pow X (by omega)
  have hLL : X ^ c ∣ L - L' := by
    have : L - L' = (α - β) - ((α - L) - (β - L')) := by ring
    rw [this]; exact dvd_sub hXcγ (hXe_c.trans (dvd_sub hXL hXL'))
  have hLLdeg : (L - L').natDegree < c := by
    refine (natDegree_sub_le _ _).trans_lt ?_
    have h1 := natDegree_lowPart_le (A.natDegree / 2) α
    have h2 := natDegree_lowPart_le (B.natDegree / 2) β
    rw [← hL] at h1; rw [← hL'] at h2
    omega
  have hLL0 : L - L' = 0 :=
    eq_zero_of_dvd_of_natDegree_lt hLL (by rw [natDegree_X_pow]; exact hLLdeg)
  have hXeγ : X ^ (2 * h + c) ∣ C (2 * k) * X ^ c * F := by
    have : C (2 * k) * X ^ c * F = ((α - L) - (β - L') + (L - L')) - X ^ (2 * h + c + c) * r := by
      linear_combination (-1 : K[X]) * hγ'
    rw [this, hLL0, add_zero]
    exact dvd_sub (dvd_sub hXL hXL') (dvd_mul_of_dvd_left (pow_dvd_pow X (by omega)) _)
  have : X ^ c * X ^ (2 * h) ∣ X ^ c * (C (2 * k) * F) := by
    rw [← pow_add, show c + 2 * h = 2 * h + c by ring]
    convert hXeγ using 1; ring
  have hX := (dvd_pow_self (X : K[X]) (by omega : 2 * h ≠ 0)).trans
    ((mul_dvd_mul_iff_left (pow_ne_zero c X_ne_zero)).mp this)
  rw [X_dvd_iff, coeff_C_mul] at hX
  exact mul_ne_zero (mul_ne_zero h2 hk) hF0 hX

/-- From the subset to the key identity: with `F = ∏_{s ∈ S} (X - s)`, `S ⊆ μ_e`, `|S| = h`,
`e = 2h + c`, and `F ^ 3` zero in degrees `h - c + 1 .. 2h - c - 1`, there are `M` of degree at most
`c` and `κ ≠ 0` with `X ^ e ∣ 1 + M F ^ 2 + κ X ^ (2c) F ^ 4` (the ODE, `K ≠ 0` and Bezout steps). -/
theorem star_of_gap {S : Finset K} {h c : ℕ} (hc : 1 ≤ c) (hch : c < h)
    (hchar : ∀ n, 0 < n → n ≤ 4 * h + c - 2 → (n : K) ≠ 0)
    (hS : S.card = h) (hroot : ∀ s ∈ S, s ^ (2 * h + c) = 1)
    (hgap : ∀ d, h - c < d → d < 2 * h - c → ((∏ s ∈ S, (X - C s)) ^ 3).coeff d = 0) :
    ∃ Mp : K[X], ∃ κ : K, κ ≠ 0 ∧ Mp.natDegree ≤ c ∧
      X ^ (2 * h + c) ∣ 1 + Mp * (∏ s ∈ S, (X - C s)) ^ 2 +
        C κ * X ^ (2 * c) * (∏ s ∈ S, (X - C s)) ^ 4 := by
  set F : K[X] := ∏ s ∈ S, (X - C s) with hF
  set e := 2 * h + c with he
  set N := 2 * h - c with hN
  set g := h - c with hg
  have hFmon : F.Monic := by simpa using monic_prod_X_sub_C (fun s : K => s) S
  have hFdeg : F.natDegree = h := (natDegree_finsetProd_X_sub_C_eq_card S (fun s : K => s)).trans hS
  have hFne : F ≠ 0 := hFmon.ne_zero
  have hs0 : ∀ s ∈ S, s ≠ 0 := by
    intro s hs h0; have := hroot s hs; rw [h0, zero_pow (by omega)] at this; exact zero_ne_one this
  have hFroot : ∀ s ∈ S, F.eval s = 0 := by
    intro s hs; rw [hF, eval_prod]; exact Finset.prod_eq_zero hs (by simp)
  have hF0 : F.coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, hF, eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun s hs => by simpa using hs0 s hs
  have hdvd : ∀ P : K[X], (∀ s ∈ S, P.eval s = 0) → F ∣ P := by
    intro P hP
    refine Finset.prod_dvd_of_coprime ?_ fun s hs => dvd_iff_isRoot.mpr (hP s hs)
    exact (pairwise_coprime_X_sub_C (s := fun s : K => s) Function.injective_id).set_pairwise _
  have he0 : (e : K) ≠ 0 := hchar e (by omega) (by omega)
  have h3 : (3 : K) ≠ 0 := by exact_mod_cast hchar 3 (by omega) (by omega)
  obtain ⟨Q, hQ⟩ : F ∣ X ^ e - 1 := hdvd _ fun s hs => by simp [hroot s hs]
  have hXe1 : (X ^ e - 1 : K[X]).natDegree = e := by
    simpa using (natDegree_X_pow_sub_C (n := e) (r := (1 : K)))
  have hQne : Q ≠ 0 := by
    rintro rfl; rw [mul_zero] at hQ
    have := congrArg natDegree hQ; rw [hXe1, natDegree_zero] at this; omega
  have hQdeg : Q.natDegree = h + c := by
    have := congrArg natDegree hQ
    rw [hXe1, natDegree_mul hFne hQne, hFdeg] at this; omega
  have hderiv : ∀ s ∈ S, (e : K) * s ^ (e - 1) = (derivative F).eval s * Q.eval s := by
    intro s hs
    have := congrArg (fun p => (derivative p).eval s) hQ
    simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul,
      eval_mul, eval_add, eval_C, eval_pow, eval_X, hFroot s hs, zero_mul, add_zero] at this
    exact this
  -- the low part `T` and the high part `Hh`
  set T := lowPart (g + 1) (F ^ 3) with hT
  set Hh := F ^ 3 - T with hHh
  have hTdeg : T.natDegree ≤ g := natDegree_lowPart_le g _
  have hHdvd : X ^ N ∣ Hh := by
    rw [X_pow_dvd_iff]; intro i hi
    rw [hHh, coeff_sub, hT, coeff_lowPart]
    split_ifs with hi'
    · ring
    · rw [sub_zero]; exact hgap i (by omega) hi
  -- the ODE step
  set W := 3 * T * derivative F - derivative T * F with hW
  have hWeq : W = derivative Hh * F - 3 * Hh * derivative F := by
    have hT' : T = F ^ 3 - Hh := by rw [hHh]; ring
    rw [hW, hT', derivative_sub, show F ^ 3 = F * F * F by ring, derivative_mul, derivative_mul]
    ring
  have hWdvd : X ^ (N - 1) ∣ W := by
    rw [hWeq]
    refine dvd_sub (dvd_mul_of_dvd_left ?_ _) (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ((pow_dvd_pow X (by omega : N - 1 ≤ N)).trans hHdvd) _) _)
    rw [X_pow_dvd_iff]; intro i hi
    rw [coeff_derivative, (X_pow_dvd_iff.mp hHdvd) (i + 1) (by omega), zero_mul]
  have hWdeg : W.natDegree ≤ N - 1 := by
    rw [hW]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine natDegree_mul_le.trans ?_
      have h1 : (3 * T).natDegree ≤ g := natDegree_mul_le.trans (by simpa using hTdeg)
      have h2 := natDegree_derivative_le F
      rw [hFdeg] at h2; omega
    · refine natDegree_mul_le.trans ?_
      have h1 := natDegree_derivative_le T
      rw [hFdeg]; omega
  set Kc := W.coeff (N - 1) with hKc
  have hWC : W = C Kc * X ^ (N - 1) := by
    ext i
    rw [coeff_C_mul_X_pow]
    split_ifs with hi
    · rw [hi]
    · rcases Nat.lt_or_gt_of_ne hi with hi | hi
      · exact (X_pow_dvd_iff.mp hWdvd) i hi
      · exact coeff_eq_zero_of_natDegree_lt (hWdeg.trans_lt hi)
  have hWs : ∀ s ∈ S, Kc * s ^ (N - 1) = 3 * T.eval s * (derivative F).eval s := by
    intro s hs
    have := congrArg (eval s) hWC
    rw [hW] at this
    simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, hFroot s hs, mul_zero, sub_zero,
      eval_ofNat] at this
    rw [← this]
  have hF's : ∀ s ∈ S, (derivative F).eval s ≠ 0 := by
    intro s hs h0
    have := hderiv s hs
    rw [h0, zero_mul] at this
    exact mul_ne_zero he0 (pow_ne_zero _ (hs0 s hs)) this
  -- `K ≠ 0`
  have hKc0 : Kc ≠ 0 := by
    intro hK0
    have hT0 : T = 0 := by
      have hFT : F ∣ T := hdvd T fun s hs => by
        have := hWs s hs
        rw [hK0, zero_mul] at this
        rcases mul_eq_zero.mp this.symm with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact absurd h'' h3
          · exact h''
        · exact absurd h' (hF's s hs)
      exact eq_zero_of_dvd_of_natDegree_lt hFT (by rw [hFdeg]; omega)
    have hX : X ∣ F ^ 3 := by
      have : X ^ N ∣ F ^ 3 := by rw [hHh, hT0, sub_zero] at hHdvd; exact hHdvd
      exact (dvd_pow_self X (by omega)).trans this
    exact hF0 (X_dvd_iff.mp (prime_X.dvd_of_dvd_pow hX))
  -- Bezout
  set κ : K := 3 * e / Kc with hκ
  have hκKc : κ * Kc = 3 * e := by rw [hκ]; field_simp
  have hκ0 : κ ≠ 0 := by rw [hκ]; exact div_ne_zero (mul_ne_zero h3 he0) hKc0
  obtain ⟨Mp, hMp⟩ : F ∣ Q - C κ * X ^ (2 * c) * T := by
    refine hdvd _ fun s hs => ?_
    have h1 := hWs s hs
    have h2 := hderiv s hs
    have hpow : s ^ (e - 1) = s ^ (N - 1) * s ^ (2 * c) := by rw [← pow_add]; congr 1; omega
    have hσ : Kc * s ^ (N - 1) ≠ 0 := mul_ne_zero hKc0 (pow_ne_zero _ (hs0 s hs))
    simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    refine (mul_eq_zero.mp ?_).resolve_left hσ
    linear_combination Q.eval s * h1 - 3 * T.eval s * h2 -
      s ^ (N - 1) * s ^ (2 * c) * T.eval s * hκKc + 3 * e * T.eval s * hpow
  have hMdeg : Mp.natDegree ≤ c := by
    by_cases hM0 : Mp = 0
    · rw [hM0, natDegree_zero]; omega
    have hZdeg : (Q - C κ * X ^ (2 * c) * T).natDegree ≤ h + c := by
      refine (natDegree_sub_le _ _).trans (max_le (le_of_eq hQdeg) ?_)
      refine natDegree_mul_le.trans ?_
      have := natDegree_C_mul_X_pow_le κ (2 * c)
      omega
    rw [hMp, natDegree_mul hFne hM0, hFdeg] at hZdeg
    omega
  obtain ⟨Hq, hHq⟩ := hHdvd
  refine ⟨Mp, κ, hκ0, hMdeg, 1 + C κ * F * Hq, ?_⟩
  have hpow2 : (X : K[X]) ^ e = X ^ (2 * c) * X ^ N := by rw [← pow_add]; congr 1; omega
  linear_combination (-F) * hMp + (-1 : K[X]) * hQ + (C κ * X ^ (2 * c) * F) * hHq +
    (-(C κ * F * Hq)) * hpow2

/-- Lemma CG over an algebraically closed field, `F`-form. -/
theorem lemmaCG_F_of_isAlgClosed [IsAlgClosed K] {h c : ℕ} (hc : 1 ≤ c) (hch : c < h)
    (hchar : ∀ n, 0 < n → n ≤ 4 * h + c - 2 → (n : K) ≠ 0)
    (S : Finset K) (hS : S.card = h) (hroot : ∀ s ∈ S, s ^ (2 * h + c) = 1) :
    ¬ ∀ d, h - c < d → d < 2 * h - c → ((∏ s ∈ S, (X - C s)) ^ 3).coeff d = 0 := by
  intro hgap
  obtain ⟨Mp, κ, hκ0, hMdeg, hstar⟩ := star_of_gap hc hch hchar hS hroot hgap
  obtain ⟨k, hk⟩ := IsAlgClosed.exists_pow_nat_eq κ (by norm_num : 0 < 2)
  have hk0 : k ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero] at hk; exact hκ0 hk.symm
  rw [← hk] at hstar
  have hFdeg : (∏ s ∈ S, (X - C s)).natDegree ≤ h :=
    le_of_eq ((natDegree_finsetProd_X_sub_C_eq_card S (fun s : K => s)).trans hS)
  have hs0 : ∀ s ∈ S, s ≠ 0 := by
    intro s hs h0; have := hroot s hs; rw [h0, zero_pow (by omega)] at this; exact zero_ne_one this
  have hF0 : (∏ s ∈ S, (X - C s)).coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun s hs => by simpa using hs0 s hs
  exact endgame hc hch hchar hk0 hF0 hFdeg hMdeg hstar

/-- **Lemma CG** (rukafe0x, result 27, Theorem CG; row M-1002), `F`-form. Let `e = 2h + c` with
`1 ≤ c ≤ h - 1`, and let the characteristic of `K` be `0` or above `4h + c - 2`. For every `h`-subset `S`
of the `e`-th roots of unity, `F = ∏_{s ∈ S} (X - s)` has `F ^ 3` nonzero in some degree `d` with
`h - c < d < 2h - c`; that is, `F ^ 3` is not `T + X ^ (h + g) H` with `deg T ≤ g = h - c`. -/
theorem lemmaCG_F {h c : ℕ} (hc : 1 ≤ c) (hch : c < h)
    (hchar : ringChar K = 0 ∨ 4 * h + c - 2 < ringChar K)
    (S : Finset K) (hS : S.card = h) (hroot : ∀ s ∈ S, s ^ (2 * h + c) = 1) :
    ¬ ∀ d, h - c < d → d < 2 * h - c → ((∏ s ∈ S, (X - C s)) ^ 3).coeff d = 0 := by
  intro hgap
  set L := AlgebraicClosure K
  set φ := algebraMap K L
  have hchar' : ∀ n, 0 < n → n ≤ 4 * h + c - 2 → (n : L) ≠ 0 := by
    intro n h0 h1 hn
    rw [← map_natCast φ, map_eq_zero_iff φ φ.injective] at hn
    exact natCast_ne_zero_of_char hchar h0 h1 hn
  let ι : K ↪ L := ⟨φ, φ.injective⟩
  have hprod : ∏ t ∈ S.map ι, (X - C t) = (∏ s ∈ S, (X - C s)).map φ := by
    rw [Finset.prod_map, Polynomial.map_prod]
    simp [ι]
  refine lemmaCG_F_of_isAlgClosed hc hch hchar' (S.map ι) (by rw [Finset.card_map, hS])
    (fun t ht => ?_) (fun d h1 h2 => ?_)
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
    simp [ι, ← map_pow, hroot s hs]
  · rw [hprod, ← Polynomial.map_pow, coeff_map, hgap d h1 h2, map_zero]

theorem reverse_prod {ι : Type*} (S : Finset ι) (f : ι → K[X]) :
    reverse (∏ i ∈ S, f i) = ∏ i ∈ S, reverse (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty]
    ext n
    rw [coeff_reverse, natDegree_one]
    rcases n with _ | n
    · simp
    · rw [revAt_eq_self_of_lt (by omega)]
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, reverse_mul_of_domain, ih]

theorem reverse_X_sub_C {s : K} (hs : s ≠ 0) : reverse (X - C s) = C (-s) * (X - C s⁻¹) := by
  ext n
  rw [coeff_reverse, natDegree_X_sub_C]
  rcases n with _ | _ | n
  · rw [revAt_le (by omega)]; simp [hs]
  · rw [revAt_le (by omega)]; simp
  · rw [revAt_eq_self_of_lt (by omega)]
    simp [coeff_X]

/-- **Lemma CG**, `A`-form (the form result 27 applies to the boundary cells): for every `h`-subset
`S` of the `e`-th roots of unity, `A = ∏_{s ∈ S} (X - s)` has `A ^ 3` nonzero in some degree `d` with
`h + c < d < e = 2h + c`. -/
theorem lemmaCG_A {h c : ℕ} (hc : 1 ≤ c) (hch : c < h)
    (hchar : ringChar K = 0 ∨ 4 * h + c - 2 < ringChar K)
    (S : Finset K) (hS : S.card = h) (hroot : ∀ s ∈ S, s ^ (2 * h + c) = 1) :
    ¬ ∀ d, h + c < d → d < 2 * h + c → ((∏ s ∈ S, (X - C s)) ^ 3).coeff d = 0 := by
  classical
  intro hgapA
  have hs0 : ∀ s ∈ S, s ≠ 0 := by
    intro s hs h0; have := hroot s hs; rw [h0, zero_pow (by omega)] at this; exact zero_ne_one this
  set A : K[X] := ∏ s ∈ S, (X - C s) with hA
  set S' := S.image (fun s : K => s⁻¹) with hS'
  have hinj : Set.InjOn (fun s : K => s⁻¹) S := fun a _ b _ hab => inv_injective hab
  set lam : K := ∏ s ∈ S, (-s) with hlam
  have hlam0 : lam ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s hs => neg_ne_zero.mpr (hs0 s hs)
  have hrevA : reverse A = C lam * ∏ t ∈ S', (X - C t) := by
    rw [hA, reverse_prod, Finset.prod_congr rfl fun s hs => reverse_X_sub_C (hs0 s hs),
      Finset.prod_mul_distrib, hlam, map_prod, hS', Finset.prod_image hinj]
  have hAmon : A.Monic := by simpa using monic_prod_X_sub_C (fun s : K => s) S
  have hAdeg : A.natDegree = h := (natDegree_finsetProd_X_sub_C_eq_card S (fun s : K => s)).trans hS
  have hA3deg : (A ^ 3).natDegree = 3 * h := by rw [hAmon.natDegree_pow, hAdeg, mul_comm]
  have hrev3 : reverse (A ^ 3) = C (lam ^ 3) * (∏ t ∈ S', (X - C t)) ^ 3 := by
    rw [show A ^ 3 = A * A * A by ring, reverse_mul_of_domain, reverse_mul_of_domain, hrevA, C_pow]
    ring
  refine lemmaCG_F hc hch hchar S' (by rw [hS', Finset.card_image_of_injOn hinj, hS])
    (fun t ht => ?_) (fun d h1 h2 => ?_)
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    rw [inv_pow, hroot s hs, inv_one]
  · have := congrArg (fun p => p.coeff d) hrev3
    simp only [coeff_C_mul, coeff_reverse, hA3deg] at this
    rw [revAt_le (by omega), hgapA (3 * h - d) (by omega) (by omega)] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero 3 hlam0)

end LemmaCG
