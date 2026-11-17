import InteriorThree_LemmaCG
import InteriorThree_M31OrbitSizeObstruction

/-!
# Lemma CG closes every M31 boundary cell `4h = N` of the single-monomial residual

Target `LEMMA` (tier 3, `problem-3a-upper`). This module wires Lemma CG (`InteriorThree_LemmaCG`, rukafe0x's
result 27, row M-1002) into omarespejel's reduction M-0998 (`InteriorThree_M31OrbitSizeObstruction`).

* `LemmaCG.lemmaCG_A_coset_of_isAlgClosed`: Lemma CG for an `h`-subset of a coset `{x : x ^ e = α}`.
* `LemmaCG.cg_boundary_cubic_obstruction`: at the boundary `e = 2h + 2k`, `f = 2h - 2k`, `1 ≤ k`,
  `2k + 1 ≤ h`, `3 ∤ e`, characteristic `0` or above `4h + 2k`, no `(A, B, Q)` with M-0998's degree
  conditions satisfies `A ^ 3 + X ^ e B ^ 3 = (X ^ (e + f) A + B) Q`. The fibre lemma
  `all_three_kummer_fibres_of_boundary_cubic` (M-0996) puts the roots of `A` on `x ^ e = -3ρ`, and the
  identity gives `A ^ 3` zero in degrees `h + 2k + 1 .. e - 1`; Lemma CG with `c = 2k` excludes this.
  No orbit-size hypothesis is needed.
* `InSingleCGBoundaryStratum` is M-0998's `InSingleM31OrbitSizeBoundaryStratum` without
  `HasM31PrimeQuotientOrbitObstruction`; `SingleMonomialResidualAfterCGBound K` is M-0998's residual
  hypothesis with that whole stratum removed; `interiorThree_of_cwStar_qPrime_cg_and_multi_sublemmas` reduces
  `MCAChallenge.InteriorThree K` to it and `MultiMonomialCanonicalCWBound K`.
-/

namespace LemmaCG

open Polynomial

variable {K : Type*} [Field K]

theorem star_of_gap_coset {S : Finset K} {h c : ℕ} {α0 : K} (hα0 : α0 ≠ 0) (hc : 1 ≤ c) (hch : c < h)
    (hchar : ∀ n, 0 < n → n ≤ 4 * h + c - 2 → (n : K) ≠ 0)
    (hS : S.card = h) (hroot : ∀ s ∈ S, s ^ (2 * h + c) = α0)
    (hgap : ∀ d, h - c < d → d < 2 * h - c → ((∏ s ∈ S, (X - C s)) ^ 3).coeff d = 0) :
    ∃ Mp : K[X], ∃ κ : K, κ ≠ 0 ∧ Mp.natDegree ≤ c ∧
      X ^ (2 * h + c) ∣ C α0 + Mp * (∏ s ∈ S, (X - C s)) ^ 2 +
        C κ * X ^ (2 * c) * (∏ s ∈ S, (X - C s)) ^ 4 := by
  set F : K[X] := ∏ s ∈ S, (X - C s) with hF
  set e := 2 * h + c with he
  set N := 2 * h - c with hN
  set g := h - c with hg
  have hFmon : F.Monic := by simpa using monic_prod_X_sub_C (fun s : K => s) S
  have hFdeg : F.natDegree = h := (natDegree_finsetProd_X_sub_C_eq_card S (fun s : K => s)).trans hS
  have hFne : F ≠ 0 := hFmon.ne_zero
  have hs0 : ∀ s ∈ S, s ≠ 0 := by
    intro s hs h0; have := hroot s hs; rw [h0, zero_pow (by omega)] at this; exact hα0 this.symm
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
  obtain ⟨Q, hQ⟩ : F ∣ X ^ e - C α0 := hdvd _ fun s hs => by simp [hroot s hs]
  have hXe1 : (X ^ e - C α0 : K[X]).natDegree = e := natDegree_X_pow_sub_C
  have hQne : Q ≠ 0 := by
    rintro rfl; rw [mul_zero] at hQ
    have := congrArg natDegree hQ; rw [hXe1, natDegree_zero] at this; omega
  have hQdeg : Q.natDegree = h + c := by
    have := congrArg natDegree hQ
    rw [hXe1, natDegree_mul hFne hQne, hFdeg] at this; omega
  have hderiv : ∀ s ∈ S, (e : K) * s ^ (e - 1) = (derivative F).eval s * Q.eval s := by
    intro s hs
    have := congrArg (fun p => (derivative p).eval s) hQ
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, derivative_mul,
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


/-- Lemma CG on a coset, `F`-form, over an algebraically closed field. -/
theorem lemmaCG_F_coset_of_isAlgClosed [IsAlgClosed K] {h c : ℕ} {α0 : K} (hα0 : α0 ≠ 0)
    (hc : 1 ≤ c) (hch : c < h)
    (hchar : ∀ n, 0 < n → n ≤ 4 * h + c - 2 → (n : K) ≠ 0)
    (S : Finset K) (hS : S.card = h) (hroot : ∀ s ∈ S, s ^ (2 * h + c) = α0) :
    ¬ ∀ d, h - c < d → d < 2 * h - c → ((∏ s ∈ S, (X - C s)) ^ 3).coeff d = 0 := by
  intro hgap
  obtain ⟨Mp, κ, hκ0, hMdeg, hstar⟩ := star_of_gap_coset hα0 hc hch hchar hS hroot hgap
  obtain ⟨k, hk⟩ := IsAlgClosed.exists_pow_nat_eq (α0⁻¹ * κ) (by norm_num : 0 < 2)
  have hk0 : k ≠ 0 := by
    rintro rfl; rw [zero_pow two_ne_zero] at hk
    exact mul_ne_zero (inv_ne_zero hα0) hκ0 hk.symm
  set F : K[X] := ∏ s ∈ S, (X - C s)
  have hstar' : X ^ (2 * h + c) ∣ 1 + (C α0⁻¹ * Mp) * F ^ 2 + C (k ^ 2) * X ^ (2 * c) * F ^ 4 := by
    have h1 : (C α0⁻¹ * C α0 : K[X]) = 1 := by rw [← C_mul, inv_mul_cancel₀ hα0, C_1]
    have : 1 + (C α0⁻¹ * Mp) * F ^ 2 + C (k ^ 2) * X ^ (2 * c) * F ^ 4 =
        C α0⁻¹ * (C α0 + Mp * F ^ 2 + C κ * X ^ (2 * c) * F ^ 4) := by
      rw [hk, C_mul]; linear_combination (-1 : K[X]) * h1
    rw [this]; exact dvd_mul_of_dvd_right hstar _
  have hFdeg : F.natDegree ≤ h :=
    le_of_eq ((natDegree_finsetProd_X_sub_C_eq_card S (fun s : K => s)).trans hS)
  have hs0 : ∀ s ∈ S, s ≠ 0 := by
    intro s hs h0; have := hroot s hs; rw [h0, zero_pow (by omega)] at this; exact hα0 this.symm
  have hF0 : F.coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun s hs => by simpa using hs0 s hs
  exact endgame hc hch hchar hk0 hF0 hFdeg ((natDegree_C_mul_le _ _).trans hMdeg) hstar'

/-- Lemma CG on a coset, `A`-form, over an algebraically closed field: for an `h`-subset `S` of
`{x : x ^ e = α0}`, `(∏_{s ∈ S} (X - s)) ^ 3` is nonzero in some degree `d`, `h + c < d < e`. -/
theorem lemmaCG_A_coset_of_isAlgClosed [IsAlgClosed K] {h c : ℕ} {α0 : K} (hα0 : α0 ≠ 0)
    (hc : 1 ≤ c) (hch : c < h)
    (hchar : ∀ n, 0 < n → n ≤ 4 * h + c - 2 → (n : K) ≠ 0)
    (S : Finset K) (hS : S.card = h) (hroot : ∀ s ∈ S, s ^ (2 * h + c) = α0) :
    ¬ ∀ d, h + c < d → d < 2 * h + c → ((∏ s ∈ S, (X - C s)) ^ 3).coeff d = 0 := by
  classical
  intro hgapA
  have hs0 : ∀ s ∈ S, s ≠ 0 := by
    intro s hs h0; have := hroot s hs; rw [h0, zero_pow (by omega)] at this; exact hα0 this.symm
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
  refine lemmaCG_F_coset_of_isAlgClosed (inv_ne_zero hα0) hc hch hchar S'
    (by rw [hS', Finset.card_image_of_injOn hinj, hS]) (fun t ht => ?_) (fun d h1 h2 => ?_)
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    rw [inv_pow, hroot s hs]
  · have := congrArg (fun p => p.coeff d) hrev3
    simp only [coeff_C_mul, coeff_reverse, hA3deg] at this
    rw [revAt_le (by omega), hgapA (3 * h - d) (by omega) (by omega)] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero 3 hlam0)

end LemmaCG

namespace InteriorThreeLemmaCGBoundary

open Polynomial Finset InteriorThreeCanonicalReduction InteriorThreeTheoremW InteriorThreeBoundaryCW
  InteriorThreeTheoremCWStar InteriorThreeKummerPrimeDivisibility InteriorThreeM31OrbitSizeObstruction

/-- **The boundary cubic has no solution, by Lemma CG.** At `e = 2h + 2k`, `f = 2h - 2k`
(`1 ≤ k`, `2k + 1 ≤ h`, `3 ∤ e`) and characteristic `0` or above `4h + 2k`, no `(A, B, Q)` with
M-0998's degree conditions satisfies `A ^ 3 + X ^ e B ^ 3 = (X ^ (e + f) A + B) Q`. -/
theorem cg_boundary_cubic_obstruction {F : Type*} [Field F] [DecidableEq F]
    {A B Q : F[X]} {h k e f : ℕ}
    (hk_pos : 1 ≤ k) (h2k_lt : 2 * k + 1 ≤ h)
    (he_eq : e = 2 * h + 2 * k) (hf_eq : f = 2 * h - 2 * k)
    (hndvd3 : ¬ (3 ∣ e))
    (hchar : ringChar F = 0 ∨ 4 * h + 2 * k < ringChar F)
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hQd : Q ≠ 0 → Q.natDegree + f ≤ 2 * h)
    (hident : A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q) : False := by
  obtain ⟨_, _, ρ, _, _, _, _, _, hρ, _, hdvdA, _⟩ :=
    all_three_kummer_fibres_of_boundary_cubic hk_pos h2k_lt he_eq hf_eq hndvd3
      (hchar.imp_right fun h' => by omega) hAm hAd hBd hB0 hQd hident
  have hcharF : ∀ n, 0 < n → n ≤ 4 * h + 2 * k → (n : F) ≠ 0 := fun n h0 h1 =>
    LemmaCG.natCast_ne_zero_of_char hchar h0 h1
  have h3 : (3 : F) ≠ 0 := by exact_mod_cast hcharF 3 (by omega) (by omega)
  have hα : (-3 * ρ : F) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h3) hρ
  -- the gap (Ga): `A ^ 3` vanishes in degrees `h + 2k + 1 .. e - 1`
  have hgap : ∀ d, h + 2 * k < d → d < e → (A ^ 3).coeff d = 0 := by
    intro d h1 h2
    have hA3 : A ^ 3 = B * Q + X ^ e * (X ^ f * A * Q - B ^ 3) := by
      rw [pow_add] at hident; linear_combination hident
    rw [hA3, coeff_add, coeff_X_pow_mul', ite_eq_right (by omega : ¬ e ≤ d), add_zero]
    by_cases hQ0 : Q = 0
    · simp [hQ0]
    · apply coeff_eq_zero_of_natDegree_lt
      have := hQd hQ0
      exact natDegree_mul_le.trans_lt (by omega)
  -- pass to the algebraic closure
  set E := AlgebraicClosure F
  set φ := algebraMap F E
  have hcharE : ∀ n, 0 < n → n ≤ 4 * h + 2 * k - 2 → (n : E) ≠ 0 := by
    intro n h0 h1 hn
    rw [← map_natCast φ, map_eq_zero_iff φ φ.injective] at hn
    exact hcharF n h0 (by omega) hn
  set AE := A.map φ with hAE
  have hAEm : AE.Monic := hAm.map φ
  have hAEd : AE.natDegree = h := by rw [hAE, natDegree_map, hAd]
  have hdvdE : AE ∣ X ^ e - C (φ (-3 * ρ)) := by
    have := Polynomial.map_dvd φ hdvdA
    simpa [Polynomial.map_sub, Polynomial.map_pow] using this
  have hαE : φ (-3 * ρ) ≠ 0 := (map_ne_zero φ).mpr hα
  have hsep : (X ^ e - C (φ (-3 * ρ))).Separable :=
    separable_X_pow_sub_C _ (hcharE e (by omega) (by omega)) hαE
  have hnd : AE.roots.Nodup := nodup_roots (hsep.of_dvd hdvdE)
  have hcard : Multiset.card AE.roots = AE.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod : (AE.roots.map fun a => X - C a).prod = AE :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hAEm hcard
  classical
  set S := AE.roots.toFinset
  have hSprod : ∏ s ∈ S, (X - C s) = AE := by
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd, hprod]
  have hScard : S.card = h := by rw [Multiset.toFinset_card_of_nodup hnd, hcard, hAEd]
  have hroot : ∀ s ∈ S, s ^ (2 * h + 2 * k) = φ (-3 * ρ) := by
    intro s hs
    rw [Multiset.mem_toFinset, mem_roots hAEm.ne_zero] at hs
    obtain ⟨g, hg⟩ := hdvdE
    have := congrArg (eval s) hg
    rw [eval_mul, hs.eq_zero, zero_mul, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at this
    rw [← he_eq]; exact this
  refine LemmaCG.lemmaCG_A_coset_of_isAlgClosed hαE (c := 2 * k) (by omega) (by omega) hcharE
    S hScard hroot ?_
  intro d h1 h2
  rw [hSprod, hAE, ← Polynomial.map_pow, coeff_map, hgap d h1 (by omega), map_zero]

private lemma not_dvd_three_pow_two : ∀ t : ℕ, ¬ (3 ∣ 2 ^ t)
  | 0 => by decide
  | t + 1 => fun hdvd ↦ by
    have hpr : Nat.Prime 3 := by decide
    rcases hpr.dvd_mul.mp (by rw [pow_succ'] at hdvd; exact hdvd) with h32 | h3t
    · revert h32; decide
    · exact not_dvd_three_pow_two t h3t

private lemma not_dvd_three_sub_pow_two {t δ : ℕ} (hlt : 2 ^ t < 3 * δ) :
    ¬ (3 ∣ (3 * δ - 2 ^ t)) := by
  intro hdvd
  have hsub : 3 ∣ 3 * δ - (3 * δ - 2 ^ t) := Nat.dvd_sub (dvd_mul_right 3 δ) hdvd
  rw [Nat.sub_sub_self (le_of_lt hlt)] at hsub
  exact not_dvd_three_pow_two t hsub

private lemma not_seven_dvd_five_mul_pow_two : ∀ t : ℕ, ¬ (7 ∣ 5 * 2 ^ t)
  | 0 => by decide
  | t + 1 => fun hdvd ↦ by
    have hpr : Nat.Prime 7 := by decide
    have hdvd' : 7 ∣ 2 * (5 * 2 ^ t) := by
      have heq : 5 * 2 ^ (t + 1) = 2 * (5 * 2 ^ t) := by rw [pow_succ]; ring
      rwa [← heq]
    rcases hpr.dvd_mul.mp hdvd' with h72 | h7t
    · revert h72; decide
    · exact not_seven_dvd_five_mul_pow_two t h7t

/-- **All-Dyadic M31 Inner-Band Vanishing on the boundary, by Lemma CG (adapted from M-0998) (`m = 5 * 2 ^ (r - 3) + δ`):**
Across every dyadic `5 ≤ r ≤ 31` (`q_oct = 2 ^ (r - 3)`), at `4 * h = 3 * q_oct - δ` (`h ≤ δ`,
`q_oct + h < 3 * δ`), NO degree-`≤ 2 ^ (r - 1)` polynomial agrees with
`C a * X ^ (5 * q_oct + δ) + R` on `(5 * q_oct + δ) - h` points of `D`, and `NativeListBound = 0`. -/
theorem ambient_and_native_vanishing_m31_cg_inner
    {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1)) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        (5 * 2 ^ (r - 3) + δ) - h ≤
          (D.filter fun x ↦
            P.eval x = (Polynomial.C a * X ^ (5 * 2 ^ (r - 3) + δ) + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) ((5 * 2 ^ (r - 3) + δ) - h)
      (Polynomial.C a * X ^ (5 * 2 ^ (r - 3) + δ) + R) 0 := by
  by_cases hlow_h : h < 2 * (2 ^ (r - 3) - δ)
  · exact ambient_and_native_vanishing_inner_band hF hr_lo hr_hi hD_card hD_pow
      hδ_pos hδ_lt hh_le hqh (Or.inr (Or.inl hlow_h)) ha R hR
  · by_cases hlow_e : 3 * h < 3 * δ - 2 ^ (r - 3)
    · exact ambient_and_native_vanishing_inner_band hF hr_lo hr_hi hD_card hD_pow
        hδ_pos hδ_lt hh_le hqh (Or.inr (Or.inr hlow_e)) ha R hR
    · have hh_ne_2qd : h ≠ 2 * (2 ^ (r - 3) - δ) := by
        intro heq
        exact not_seven_dvd_five_mul_pow_two (r - 3) ⟨δ, by omega⟩
      have h3h_ne_e : 3 * h ≠ 3 * δ - 2 ^ (r - 3) := by
        intro heq
        exact not_dvd_three_pow_two (r - 3) ⟨δ - h, by rw [Nat.mul_sub]; omega⟩
      have hk_lo : 2 * (2 ^ (r - 3) - δ) < h := by omega
      have h3h_gt_e : 3 * δ - 2 ^ (r - 3) < 3 * h := by omega
      have hno_amb :
          ¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
            (5 * 2 ^ (r - 3) + δ) - h ≤
              (D.filter fun x ↦
                P.eval x = (Polynomial.C a * X ^ (5 * 2 ^ (r - 3) + δ) + R).eval x).card := by
        rintro ⟨P, hP_deg, hcard_ge⟩
        set q_oct := 2 ^ (r - 3)
        set m := 5 * q_oct + δ
        set S := D.filter fun x ↦ P.eval x = (Polynomial.C a * X ^ m + R).eval x
        have hSD : S ⊆ D := Finset.filter_subset _ _
        have hS_ge_5q : 5 * q_oct ≤ S.card := by omega
        have hP_ag : ∀ x ∈ S, P.eval x = (Polynomial.C a * X ^ m + R).eval x :=
          fun x hx ↦ (Finset.mem_filter.mp hx).2
        set h₀ := m - S.card
        have hh₀_le_h : h₀ ≤ h := by omega
        have hqh₀ : q_oct + h₀ < 3 * δ := by omega
        obtain ⟨h', A, B, Q, hh'_le_h₀, hAm, hAd, hBd, hB0, hQd, hident⟩ :=
          two_block_cubic_certificate hF hr_lo hr_hi hD_card hD_pow hSD hδ_pos hδ_lt ha hR hP_deg
            hS_ge_5q hP_ag hqh₀
        have hh'_le_h : h' ≤ h := le_trans hh'_le_h₀ hh₀_le_h
        have he_pos : 0 < 3 * δ - q_oct := by omega
        have hf_pos : 0 < 4 * (q_oct - δ) := by omega
        have hndvd : ¬ (3 ∣ (3 * δ - q_oct)) :=
          not_dvd_three_sub_pow_two (by omega : 2 ^ (r - 3) < 3 * δ)
        have hrchar : ringChar F = 2 ^ 31 - 1 := mersenne_ext_ringChar hF
        have : CharP F (2 ^ 31 - 1) := ringChar.of_eq hrchar
        have hq_le : q_oct ≤ 2 ^ 28 := Nat.pow_le_pow_right (by decide) (by omega : r - 3 ≤ 28)
        rcases lt_or_eq_of_le hh'_le_h with hh'_lt | rfl
        · have hchar : ringChar F = 0 ∨ 3 * h' < ringChar F :=
            Or.inr (by rw [hrchar]; omega)
          exact wronskian_cubic_obstruction hAm hAd hBd hB0 he_pos hf_pos hndvd hchar hQd
            (by omega : 4 * h' < (3 * δ - q_oct) + 4 * (q_oct - δ)) hident
        · let k : ℕ := h' - 2 * (q_oct - δ)
          exact cg_boundary_cubic_obstruction (k := k)
            (by omega : 1 ≤ k)
            (by omega : 2 * k + 1 ≤ h')
            (by omega : 3 * δ - q_oct = 2 * h' + 2 * k)
            (by omega : 4 * (q_oct - δ) = 2 * h' - 2 * k)
            hndvd
            (Or.inr (by rw [hrchar]; omega))
            hAm hAd hBd hB0 hQd hident
      refine ⟨hno_amb, fun L hL ↦ ?_⟩
      have hL_empty : L = ∅ := by
        by_contra hne
        obtain ⟨P, hP_mem⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        obtain ⟨hP_nat, hP_ag⟩ := hL P hP_mem
        exact hno_amb ⟨P, hP_nat.1, hP_ag⟩
      rw [hL_empty, Finset.card_empty, Nat.cast_zero]

/-- **Mirror Duality (`m = 7 * 2 ^ (r - 3) - δ`) at `4 * h = 3 * 2 ^ (r - 3) - δ`:**
Extends `ambient_and_native_vanishing_m31_cg_inner` to `m = 7 * 2 ^ (r - 3) - δ` via
Mersenne circle Frobenius inversion `x ^ p = x⁻¹` (`p = 2 ^ 31 - 1`). -/
theorem ambient_and_native_vanishing_m31_cg_mirror
    {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1)) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        (5 * 2 ^ (r - 3) + δ) - h ≤
          (D.filter fun x ↦
            P.eval x = (Polynomial.C a * X ^ (7 * 2 ^ (r - 3) - δ) + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) ((5 * 2 ^ (r - 3) + δ) - h)
      (Polynomial.C a * X ^ (7 * 2 ^ (r - 3) - δ) + R) 0 := by
  have hrchar : ringChar F = 2 ^ 31 - 1 := mersenne_ext_ringChar hF
  have : CharP F (2 ^ 31 - 1) := ringChar.of_eq hrchar
  have hinv := mersenne_frobenius_inv_on_D hr_hi hD_pow
  obtain ⟨_, hr1_raw, hr0_raw⟩ := dyadic_octant_identities (by omega : 4 ≤ r)
  let p : ℕ := 2 ^ 31 - 1
  let q_oct : ℕ := 2 ^ (r - 3)
  let K : ℕ := 2 ^ (r - 1)
  have hr1 : K = 4 * q_oct := hr1_raw
  have hr0 : 2 ^ r = 8 * q_oct := hr0_raw
  let conjRev : F[X] → F[X] := fun Q ↦
    ∑ j ∈ Finset.range (K + 1), Polynomial.C ((Q.coeff j) ^ p) * X ^ (K - j)
  have hconjRev_deg : ∀ Q : F[X], (conjRev Q).natDegree ≤ K := by
    intro Q
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le K, fun j _ ↦ ?_⟩
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    exact le_trans (Polynomial.natDegree_X_pow_le _) (by omega)
  have hconjRev_eval : ∀ Q : F[X], Q.natDegree ≤ K → ∀ x ∈ D,
      (conjRev Q).eval x = x ^ K * (Q.eval x) ^ p := by
    intro Q hQd x hxD
    have hxp_inv : x ^ p = x⁻¹ := (hinv x hxD).2
    have hx_ne : x ≠ 0 := fun h0 ↦ by
      have h1 := hD_pow x hxD
      rw [h0, zero_pow (by positivity)] at h1
      exact zero_ne_one h1
    have hQ_sum : Q.eval x = ∑ j ∈ Finset.range (K + 1), Q.coeff j * x ^ j := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQd)]
    have hfrob_sum : (Q.eval x) ^ p = ∑ j ∈ Finset.range (K + 1), (Q.coeff j) ^ p * (x ^ p) ^ j := by
      rw [hQ_sum]
      have hmap := map_sum (frobenius F p) (fun j ↦ Q.coeff j * x ^ j) (Finset.range (K + 1))
      change (∑ j ∈ Finset.range (K + 1), Q.coeff j * x ^ j) ^ p =
        ∑ j ∈ Finset.range (K + 1), (Q.coeff j * x ^ j) ^ p at hmap
      rw [hmap]
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      rw [mul_pow, pow_right_comm]
    rw [hfrob_sum, Finset.mul_sum]
    simp only [conjRev, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, hxp_inv]
    refine Finset.sum_congr rfl (fun j hj ↦ ?_)
    have hj_le : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hxk : x ^ K = x ^ (K - j) * x ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj_le]
    have hxinv_j : (x⁻¹) ^ j * x ^ j = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hx_ne, one_pow]
    calc (Q.coeff j) ^ p * x ^ (K - j)
        = (Q.coeff j) ^ p * x ^ (K - j) * ((x⁻¹) ^ j * x ^ j) := by rw [hxinv_j, mul_one]
      _ = (x ^ (K - j) * x ^ j) * ((Q.coeff j) ^ p * (x⁻¹) ^ j) := by ring
      _ = x ^ K * ((Q.coeff j) ^ p * (x⁻¹) ^ j) := by rw [hxk]
  have hap_ne : a ^ p ≠ 0 := pow_ne_zero p ha
  have hinner := ambient_and_native_vanishing_m31_cg_inner hF hr_lo hr_hi
    hD_card hD_pow hδ_pos hδ_lt hh_le hqh hbdry hap_ne (conjRev R) (hconjRev_deg R)
  have hno_mirror :
      ¬ ∃ P : F[X], P.natDegree ≤ K ∧
        (5 * q_oct + δ) - h ≤
          (D.filter fun x ↦
            P.eval x = (Polynomial.C a * X ^ (7 * q_oct - δ) + R).eval x).card := by
    rintro ⟨P, hP_deg, hcard⟩
    apply hinner.1
    refine ⟨conjRev P, hconjRev_deg P, le_trans hcard (Finset.card_le_card ?_)⟩
    intro x hx
    obtain ⟨hxD, hx_eq⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxD, ?_⟩
    have hxp_inv : x ^ p = x⁻¹ := (hinv x hxD).2
    have hx8q : x ^ (8 * q_oct) = 1 := by rw [← hr0]; exact hD_pow x hxD
    have hx_ne : x ≠ 0 := fun h0 ↦ by
      rw [h0, zero_pow (by omega : 8 * q_oct ≠ 0)] at hx8q
      exact zero_ne_one hx8q
    have hx_mirror_pow : x ^ K * (x ^ (7 * q_oct - δ)) ^ p = x ^ (5 * q_oct + δ) := by
      rw [pow_right_comm, hxp_inv]
      have hprod1 : (x⁻¹) ^ (7 * q_oct - δ) * x ^ (7 * q_oct - δ) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hx_ne, one_pow]
      have hexp_eq : K + 8 * q_oct = (5 * q_oct + δ) + (7 * q_oct - δ) := by omega
      calc x ^ K * (x⁻¹) ^ (7 * q_oct - δ)
          = x ^ K * 1 * (x⁻¹) ^ (7 * q_oct - δ) := by rw [mul_one]
        _ = x ^ K * x ^ (8 * q_oct) * (x⁻¹) ^ (7 * q_oct - δ) := by rw [hx8q]
        _ = x ^ (K + 8 * q_oct) * (x⁻¹) ^ (7 * q_oct - δ) := by rw [← pow_add]
        _ = (x ^ (5 * q_oct + δ) * x ^ (7 * q_oct - δ)) * (x⁻¹) ^ (7 * q_oct - δ) := by
            rw [hexp_eq, pow_add]
        _ = x ^ (5 * q_oct + δ) * ((x⁻¹) ^ (7 * q_oct - δ) * x ^ (7 * q_oct - δ)) := by ring
        _ = x ^ (5 * q_oct + δ) := by rw [hprod1, mul_one]
    rw [hconjRev_eval P hP_deg x hxD, hx_eq]
    have hfrob_add :
        ((Polynomial.C a * X ^ (7 * q_oct - δ) + R).eval x) ^ p =
          a ^ p * (x ^ (7 * q_oct - δ)) ^ p + (R.eval x) ^ p := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      have hm := map_add (frobenius F p) (a * x ^ (7 * q_oct - δ)) (R.eval x)
      change (a * x ^ (7 * q_oct - δ) + R.eval x) ^ p =
        (a * x ^ (7 * q_oct - δ)) ^ p + (R.eval x) ^ p at hm
      rw [hm, mul_pow]
    rw [hfrob_add, mul_add, ← mul_assoc (x ^ K), mul_comm (x ^ K) (a ^ p), mul_assoc (a ^ p),
      hx_mirror_pow, ← hconjRev_eval R hR x hxD]
    dsimp only [q_oct]
    simp
  refine ⟨hno_mirror, fun L hL ↦ ?_⟩
  have hL_empty : L = ∅ := by
    by_contra hne
    obtain ⟨P, hP_mem⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨hP_nat, hP_ag⟩ := hL P hP_mem
    exact hno_mirror ⟨P, hP_nat.1, hP_ag⟩
  rw [hL_empty, Finset.card_empty, Nat.cast_zero]

/-- The boundary stratum `4 u + 5 δ = 15 q` (`u < 2 (q + δ)`) of M-0998's
`InSingleM31OrbitSizeBoundaryStratum`, without the orbit-size condition. -/
def InSingleCGBoundaryStratum (r m u : ℕ) : Prop :=
  5 ≤ r ∧
  ∃ δ : ℕ, 1 ≤ δ ∧ δ < 2 ^ (r - 3) ∧
    (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) ∧
    u < 2 * (2 ^ (r - 3) + δ) ∧
    4 * u + 5 * δ = 15 * 2 ^ (r - 3)

/-- All-dyadic M31 boundary complement-vanishing proposition (no orbit-size condition) across `5 ≤ r ≤ 31`. -/
def SingleMonomialCGBoundaryVanishing.{u} : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 5 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ δ : ℕ, 1 ≤ δ → δ < 2 ^ (r - 3) →
        ∀ m : ℕ, (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) →
          ∀ (γ : F) (U : Finset F),
            U.card < 2 * (2 ^ (r - 3) + δ) →
            4 * U.card + 5 * δ = 15 * 2 ^ (r - 3) →
            ¬ IsValidCWComplement D r ((X : F[X]) ^ m) γ U

/-- **Every M31 boundary cell is empty:** `¬ IsValidCWComplement D r (X ^ m) γ U` on the whole
boundary stratum, at every dyadic `5 ≤ r ≤ 31`, by Lemma CG. -/
theorem singleMonomialCGBoundaryVanishing.{u} :
    SingleMonomialCGBoundaryVanishing.{u} := by
  intro F _ _ hF r hr5 hr_hi D hD_card hD_pow δ hδ1 hδ_lt m hm_eq γ U hu_lt hbdry_u hvalid
  have hr4 : 4 ≤ r := by omega
  obtain ⟨_, _, hr0⟩ := dyadic_octant_identities hr4
  obtain ⟨hUD, hu_le_3q, _, _, hB_deg, _, _⟩ := hvalid
  let S : Finset F := D \ U
  have hSD : S ⊆ D := Finset.sdiff_subset
  have hDS : D \ S = U := Finset.sdiff_sdiff_eq_self hUD
  have hu_add_S : S.card + U.card = 8 * 2 ^ (r - 3) := by
    have hsdiff := Finset.card_sdiff_add_card_eq_card hUD
    change S.card + U.card = D.card at hsdiff
    rw [hD_card, hr0] at hsdiff
    exact hsdiff
  have hS_ge_5q : 5 * 2 ^ (r - 3) ≤ S.card := by omega
  have hB_deg' :
      (((X : F[X]) ^ m * ∏ x ∈ D \ S, (X - Polynomial.C x)) %ₘ
        ((X : F[X]) ^ (2 ^ r) - 1)).natDegree ≤ 2 ^ (r - 1) + (D \ S).card := by
    rwa [hDS]
  obtain ⟨P, hP_deg, hP_ag⟩ :=
    (weierstrass_silent_band_iff hr4 hD_card hD_pow hSD hS_ge_5q ((X : F[X]) ^ m)).1.mpr hB_deg'
  have hS_filt :
      S.card ≤
        (D.filter fun x ↦ P.eval x = (Polynomial.C (1 : F) * X ^ m + 0).eval x).card := by
    refine Finset.card_le_card (fun x hxS ↦ Finset.mem_filter.mpr ⟨hSD hxS, ?_⟩)
    rw [map_one, one_mul, add_zero]
    exact hP_ag x hxS
  let h : ℕ := U.card + δ - 3 * 2 ^ (r - 3)
  have hh_le : h ≤ δ := by omega
  have hqh : 2 ^ (r - 3) + h < 3 * δ := by omega
  have hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ := by omega
  have hk_eq : h - 2 * (2 ^ (r - 3) - δ) = U.card + 3 * δ - 5 * 2 ^ (r - 3) := by omega
  have hS_eq : (5 * 2 ^ (r - 3) + δ) - h = S.card := by omega
  rcases hm_eq with rfl | rfl
  · exact (ambient_and_native_vanishing_m31_cg_inner hF hr5 hr_hi
      hD_card hD_pow hδ1 hδ_lt hh_le hqh hbdry one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩
  · exact (ambient_and_native_vanishing_m31_cg_mirror hF hr5 hr_hi
      hD_card hD_pow hδ1 hδ_lt hh_le hqh hbdry one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩


/-- The single-monomial residual after Theorem W, CW*, Lemma Q'_ℓ and the whole M31 boundary
`4u + 5δ = 15q` (Lemma CG): M-0998's `SingleMonomialResidualAfterOrbitSizeBound` with the orbit-size
stratum replaced by the full boundary stratum `InSingleCGBoundaryStratum`. -/
def SingleMonomialResidualAfterCGBound.{u} (K : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 4 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ m : ℕ, 5 * 2 ^ (r - 3) ≤ m → m ≤ 7 * 2 ^ (r - 3) → ∀ γ : F,
        ∀ 𝒰 : Finset (Finset F),
          (∀ U ∈ 𝒰,
            IsValidCWComplement D r ((X : F[X]) ^ m) γ U ∧
            ¬ InSingleWronskianStratum r m U.card ∧
            ¬ InSingleFullFrobeniusBoundaryStratum r m U.card ∧
            ¬ InSingleQPrimeBoundaryStratum r m U.card ∧
            ¬ InSingleCGBoundaryStratum r m U.card) →
          𝒰.card ≤ K * 2 ^ r

/-- The orbit-size stratum of M-0998 lies inside the CG boundary stratum. -/
theorem inSingleCGBoundaryStratum_of_orbitSize {r m u : ℕ}
    (h : InSingleM31OrbitSizeBoundaryStratum r m u) : InSingleCGBoundaryStratum r m u := by
  obtain ⟨hr5, δ, hδ1, hδ_lt, hm_eq, hu_lt, hbdry, _⟩ := h
  exact ⟨hr5, δ, hδ1, hδ_lt, hm_eq, hu_lt, hbdry⟩

/-- `SingleMonomialResidualAfterCGBound K` implies M-0998's
`SingleMonomialResidualAfterOrbitSizeBound K`: a valid complement never lies in the CG stratum. -/
theorem singleMonomialResidualAfterOrbitSize_of_after_CG.{u} {K : ℕ}
    (hRem : SingleMonomialResidualAfterCGBound.{u} K) :
    SingleMonomialResidualAfterOrbitSizeBound.{u} K := by
  intro F _ _ hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 h𝒰
  refine hRem F hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 (fun U hUm ↦ ?_)
  obtain ⟨hvalid, hnotW, hnotCWStar, hnotQP, _⟩ := h𝒰 U hUm
  refine ⟨hvalid, hnotW, hnotCWStar, hnotQP, ?_⟩
  rintro ⟨hr5, δ, hδ1, hδ_lt, hm_eq, hu_lt, hbdry⟩
  exact singleMonomialCGBoundaryVanishing F hF r hr5 hr_hi D hD_card hD_pow
    δ hδ1 hδ_lt m hm_eq γ U hu_lt hbdry hvalid

/-- **`MCAChallenge.InteriorThree K` reduced to the residual after Lemma CG** and
`MultiMonomialCanonicalCWBound K` (`1 ≤ K ≤ 2 ^ 20`, every dyadic `4 ≤ r ≤ 31`). -/
theorem interiorThree_of_cwStar_qPrime_cg_and_multi_sublemmas.{u} {K : ℕ}
    (hK_pos : 1 ≤ K) (hK_cap : K ≤ 2 ^ 20)
    (hRem : SingleMonomialResidualAfterCGBound.{u} K)
    (hMulti : MultiMonomialCanonicalCWBound.{u} K) :
    MCAChallenge.InteriorThree.{u} K :=
  interiorThree_of_cwStar_qPrime_orbitSize_and_multi_sublemmas hK_pos hK_cap
    (singleMonomialResidualAfterOrbitSize_of_after_CG hRem) hMulti

end InteriorThreeLemmaCGBoundary
