import MCAChallenge
import InteriorThree_CanonicalReduction
import InteriorThree_TheoremW
import InteriorThree_BoundaryCW
import InteriorThree_TheoremCWStar
import InteriorThree_KummerPrimeDivisibility
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Kummer Prime-Quotient Frobenius Orbit-Size Obstruction (`@rukafe0x` Result 15, `M-0966`)
# All-Dyadic `5 ≤ r ≤ 31` Non-Frobenius Boundary Vanishing & `MCAChallenge.InteriorThree K` Narrowing

Importing `InteriorThree_CanonicalReduction`, `InteriorThree_TheoremW`, `InteriorThree_BoundaryCW`,
`InteriorThree_TheoremCWStar`, and `InteriorThree_KummerPrimeDivisibility`, this module formalizes
and generalizes `@rukafe0x`'s Result 15 (`M-0966`, `bp1_f1098e2976f6669b41d03930`) across **every
dyadic scale** `n = 2 ^ r` (`5 ≤ r ≤ 31`, `q_oct = 2 ^ (r - 3)`) over the Mersenne extension field
`F` (`Nat.card F = (2 ^ 31 - 1) ^ 2`), eliminating Wronskian-boundary cells
`4 * U.card + 5 * δ = 15 * 2 ^ (r - 3)` (`4 * h = 3 * 2 ^ (r - 3) - δ`) where `Theorem CW*` fails
(`-1 ∉ ⟨p mod e⟩`) AND `Lemma Q'_ℓ` does not apply (`gcd(e, p - 1)` has no odd prime divisor):

1. **General Finite-Field Kummer Prime-Quotient Frobenius Orbit-Size Theorem
   (`kummer_prime_quotient_frobenius_orbit_remainder`):**
   Over any finite field `F` of prime characteristic `p` and cardinality `Nat.card F = p ^ s`
   (`1 ≤ s`), let `M : F[X]` be monic of degree `d` dividing `X ^ e - C α` (`α ∈ F \ {0}`, `1 ≤ e`,
   `e < p`). Suppose `q` is a prime dividing `e` (`g₀ = e / q`) with `¬ (q ∣ (p ^ s - 1))`, and
   `L ≥ 1` is the multiplicative order of `p ^ s` modulo `q` (`q ∣ (p ^ s) ^ L - 1` and
   `∀ m, 1 ≤ m → m < L → ¬ (q ∣ (p ^ s) ^ m - 1)`):
   - Since `Nat.Coprime q (p ^ s - 1)` and `α ^ (p ^ s - 1) = 1`, Bézout gives an `F`-rational root
     `w₀ ∈ F \ {0}` with `w₀ ^ q = α` and `w₀ ^ (p ^ s) = w₀`.
   - Over `E = AlgebraicClosure F`, `R_M = (M.map (algebraMap F E)).roots.toFinset` (`R_M.card = d`)
     splits into `R_fix = { z ∈ R_M | z ^ g₀ = w₀ }` (`R_fix.card ≤ g₀ = e / q`) and its complement
     `R_orb = R_M \ R_fix`, which is invariant under the injective `F`-Frobenius `z ↦ z ^ (p ^ s)`.
   - Every periodic orbit of `z ↦ z ^ (p ^ s)` on `R_orb` has length `m` satisfying
     `((z ^ g₀) * w₀⁻¹) ^ ((p ^ s) ^ m - 1) = 1` with `(z ^ g₀) * w₀⁻¹ ≠ 1` of prime order `q`,
     forcing `q ∣ ((p ^ s) ^ m - 1)` and hence `L ∣ m`. Partitioning `R_orb` into Frobenius orbits
     yields `L ∣ R_orb.card`, so whenever `e / q < L`, **`d % L ≤ e / q`**!

2. **Two-Fibre Boundary Cubic Obstruction (`lemma_m31_orbit_size_cubic_obstruction`):**
   Combining `all_three_kummer_fibres_of_boundary_cubic` (`M-0959`, Result 8) with
   `kummer_prime_quotient_frobenius_orbit_remainder` on both `A` (`d = h`) and `Q₁` (`d = 2 * k`)
   over `Nat.card F = p ^ 2` (`4 * h < p`) forces **`h % L ≤ e / q ∧ (2 * k) % L ≤ e / q`**,
   eliminating every boundary cell with `e / q < h % L ∨ e / q < (2 * k) % L`.

3. **All-Dyadic `5 ≤ r ≤ 31` Vanishing, Composable Reduction, & 11 Concrete Boundary Corollaries:**
   - Proves `singleMonomialM31OrbitSizeBoundaryVanishing.{u}`, narrows
     `SingleMonomialResidualAfterCWStarAndQPrimeBound.{u} K` to
     `SingleMonomialResidualAfterOrbitSizeBound.{u} K`, and establishes
     `interiorThree_of_cwStar_qPrime_orbitSize_and_multi_sublemmas.{u}` for `MCAChallenge.InteriorThree K`.
   - Constructively certifies via pure kernel reduction `NativeListBound = 0` on all 3 orbit-size cells
     at `n = 2048` (`(δ, h) ∈ {(196, 143), (204, 141), (220, 137)}`) and all 8 orbit-size cells at
     `n = 4096` — including all 5 newly closed non-Frobenius Result 15 cells
     `(δ, h) ∈ {(380, 289), (388, 287), (408, 282), (412, 281), (428, 277)}` plus
     `{(392, 286), (436, 275), (440, 274)}`.
-/

namespace InteriorThreeM31OrbitSizeObstruction

open Polynomial Finset InteriorThreeCanonicalReduction InteriorThreeTheoremW
  InteriorThreeBoundaryCW InteriorThreeTheoremCWStar InteriorThreeKummerPrimeDivisibility

/-! ## Part 1: Fuel-Bounded Binary Exponentiation & Constructive Multiplicative-Order Certificates -/

/-- Fuel-bounded binary modular exponentiation computing `(b ^ e) % m` in `O(fuel)` steps. -/
def powModBin : ℕ → ℕ → ℕ → ℕ → ℕ
  | _, _, 0, m => 1 % m
  | 0, b, e, m => (b ^ e) % m
  | fuel + 1, b, e, m =>
    let half := powModBin fuel b (e / 2) m
    let sq := (half * half) % m
    if e % 2 = 0 then sq else (sq * (b % m)) % m

private lemma powModBin_eq : ∀ (fuel b e m : ℕ), powModBin fuel b e m = (b ^ e) % m
  | _, _, 0, _ => by simp [powModBin]
  | 0, _, _ + 1, _ => by simp [powModBin]
  | fuel + 1, b, e + 1, m => by
    have ih := powModBin_eq fuel b ((e + 1) / 2) m
    have hdiv : 2 * ((e + 1) / 2) + (e + 1) % 2 = e + 1 := Nat.div_add_mod (e + 1) 2
    have hlt : (e + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases hrem : (e + 1) % 2 = 0
    · have hexp : e + 1 = (e + 1) / 2 + (e + 1) / 2 := by omega
      simp only [powModBin, hrem, ↓reduceIte, ih]
      rw [← Nat.mul_mod, ← pow_add, ← hexp]
    · have hexp : e + 1 = ((e + 1) / 2 + (e + 1) / 2) + 1 := by omega
      simp only [powModBin, hrem, ↓reduceIte, ih]
      rw [← Nat.mul_mod (b ^ ((e + 1) / 2)) (b ^ ((e + 1) / 2)) m,
        ← Nat.mul_mod, ← pow_add, ← pow_succ, ← hexp]

private lemma pow_mod_eq_mod_pow_mod (a : ℕ) : ∀ (m q : ℕ), (a ^ m) % q = ((a % q) ^ m) % q
  | 0, q => by simp
  | m + 1, q => by
    calc (a ^ (m + 1)) % q
        = ((a ^ m % q) * (a % q)) % q := by rw [pow_succ, Nat.mul_mod]
      _ = ((((a % q) ^ m) % q) * ((a % q) % q)) % q := by
            rw [pow_mod_eq_mod_pow_mod a m q, Nat.mod_mod]
      _ = ((a % q) ^ (m + 1)) % q := by rw [← Nat.mul_mod, ← pow_succ]

private lemma dvd_sub_one_iff_mod_eq_one {X q : ℕ} (hX : 1 ≤ X) (hq : 2 ≤ q) :
    q ∣ (X - 1) ↔ X % q = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    have hX_eq : X = q * k + 1 := by omega
    rw [hX_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hq]
  · intro hmod
    refine ⟨X / q, ?_⟩
    have hdiv := Nat.div_add_mod X q
    omega

/-- Structural trial-division check over `d, d + 1, ..., d + cnt - 1`. -/
def noDivStep : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | cnt + 1, d, n => (n % d != 0) && noDivStep cnt (d + 1) n

private lemma noDivStep_iff :
    ∀ (cnt d n : ℕ), noDivStep cnt d n = true ↔ ∀ j < cnt, n % (d + j) ≠ 0
  | 0, _, _ => by simp [noDivStep]
  | cnt + 1, d, n => by
    simp only [noDivStep, Bool.and_eq_true, bne_iff_ne, ne_eq, noDivStep_iff cnt (d + 1) n]
    constructor
    · rintro ⟨h0, hrest⟩ j hj
      rcases j with _ | j
      · simpa using h0
      · have h := hrest j (by omega)
        have heq : d + 1 + j = d + (j + 1) := by omega
        rwa [heq] at h
    · intro hall
      refine ⟨by simpa using hall 0 (by omega), fun j hj ↦ ?_⟩
      have h := hall (j + 1) (by omega)
      have heq : d + 1 + j = d + (j + 1) := by omega
      rwa [heq]

private lemma prime_of_noDivStep {q B : ℕ} (hq2 : 2 ≤ q) (hsq : q < (B + 2) ^ 2)
    (hstep : noDivStep B 2 q = true) :
    Nat.Prime q := by
  have hndiv := (noDivStep_iff B 2 q).mp hstep
  by_contra hnp
  have hmp : Nat.Prime q.minFac := Nat.minFac_prime (by omega)
  have hmd : q.minFac ∣ q := Nat.minFac_dvd q
  have hmsq : q.minFac ^ 2 ≤ q := Nat.minFac_sq_le_self (by omega) hnp
  have hltB : q.minFac - 2 < B := by
    by_contra hge
    have h1 : B + 2 ≤ q.minFac := by have := hmp.two_le; omega
    have h2 : (B + 2) ^ 2 ≤ q.minFac ^ 2 := Nat.pow_le_pow_left h1 2
    omega
  have heq : 2 + (q.minFac - 2) = q.minFac := by have := hmp.two_le; omega
  have hne := hndiv (q.minFac - 2) hltB
  rw [heq] at hne
  exact hne (Nat.mod_eq_zero_of_dvd hmd)

/-- Structural non-unit-power check over exponents `m, m + 1, ..., m + cnt - 1`. -/
def noUnitPowStep : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => true
  | cnt + 1, m, b, q => (powModBin 8 b m q != 1) && noUnitPowStep cnt (m + 1) b q

private lemma noUnitPowStep_iff :
    ∀ (cnt m b q : ℕ),
      noUnitPowStep cnt m b q = true ↔ ∀ j < cnt, powModBin 8 b (m + j) q ≠ 1
  | 0, _, _, _ => by simp [noUnitPowStep]
  | cnt + 1, m, b, q => by
    simp only [noUnitPowStep, Bool.and_eq_true, bne_iff_ne, ne_eq,
      noUnitPowStep_iff cnt (m + 1) b q]
    constructor
    · rintro ⟨h0, hrest⟩ j hj
      rcases j with _ | j
      · simpa using h0
      · have h := hrest j (by omega)
        have heq : m + 1 + j = m + (j + 1) := by omega
        rwa [heq] at h
    · intro hall
      refine ⟨by simpa using hall 0 (by omega), fun j hj ↦ ?_⟩
      have h := hall (j + 1) (by omega)
      have heq : m + 1 + j = m + (j + 1) := by omega
      rwa [heq]

/-- Constructive kernel certificate that `q < 225` is prime and `L ≥ 2` is the exact multiplicative
order of `(2 ^ 31 - 1) ^ 2` modulo `q`. -/
def certM31OrbitPrime (q L : ℕ) : Bool :=
  let b := ((2 ^ 31 - 1) ^ 2) % q
  decide (2 ≤ q) && decide (q < 15 ^ 2) && noDivStep 13 2 q &&
  decide (2 ≤ L) && (powModBin 8 b L q == 1) && noUnitPowStep (L - 1) 1 b q

/-- Soundness of `certM31OrbitPrime`: certifies `Nat.Prime q`, `¬ (q ∣ ((2 ^ 31 - 1) ^ 2 - 1))`,
and that `L` is the exact multiplicative order of `(2 ^ 31 - 1) ^ 2` modulo `q`. -/
theorem certM31OrbitPrime_sound {q L : ℕ} (hcert : certM31OrbitPrime q L = true) :
    Nat.Prime q ∧
    1 ≤ L ∧
    ¬ (q ∣ ((2 ^ 31 - 1) ^ 2 - 1)) ∧
    q ∣ (((2 ^ 31 - 1) ^ 2) ^ L - 1) ∧
    (∀ m : ℕ, 1 ≤ m → m < L → ¬ (q ∣ (((2 ^ 31 - 1) ^ 2) ^ m - 1))) := by
  unfold certM31OrbitPrime at hcert
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcert
  rcases hcert with ⟨⟨⟨⟨⟨hq2, hq_lt⟩, hdiv⟩, hL2⟩, hpowL⟩, hmin⟩
  have hprime : Nat.Prime q := prime_of_noDivStep hq2 hq_lt hdiv
  let Q_M : ℕ := (2 ^ 31 - 1) ^ 2
  let b : ℕ := Q_M % q
  have hQM_pos : 1 ≤ Q_M := by dsimp only [Q_M]; decide
  have hpowL_eq : (Q_M ^ L) % q = 1 := by
    rw [pow_mod_eq_mod_pow_mod Q_M L q, ← powModBin_eq 8 b L q]
    exact hpowL
  have hdvd_L : q ∣ (Q_M ^ L - 1) :=
    (dvd_sub_one_iff_mod_eq_one (Nat.one_le_pow L Q_M hQM_pos) hq2).mpr hpowL_eq
  have hmin_step := (noUnitPowStep_iff (L - 1) 1 b q).mp hmin
  have hnot_below : ∀ m : ℕ, 1 ≤ m → m < L → ¬ (q ∣ (Q_M ^ m - 1)) := by
    intro m hm1 hm_lt hdvd_m
    have hmod1 : (Q_M ^ m) % q = 1 :=
      (dvd_sub_one_iff_mod_eq_one (Nat.one_le_pow m Q_M hQM_pos) hq2).mp hdvd_m
    have hbin1 : powModBin 8 b m q = 1 := by
      rw [powModBin_eq 8 b m q, ← pow_mod_eq_mod_pow_mod Q_M m q]
      exact hmod1
    have hj_lt : m - 1 < L - 1 := by omega
    have hm_eq : 1 + (m - 1) = m := by omega
    have hne := hmin_step (m - 1) hj_lt
    rw [hm_eq] at hne
    exact hne hbin1
  have hnot_one : ¬ (q ∣ (Q_M - 1)) := by
    have h1 := hnot_below 1 (le_refl 1) hL2
    rwa [pow_one] at h1
  exact ⟨hprime, by omega, hnot_one, hdvd_L, hnot_below⟩

/-! ## Part 2: Orbit-Divisibility Combinatorics for Injective Finite-Set Self-Maps -/

private lemma injOn_iterate_of_mapsTo {α : Type*} {S : Finset α} {f : α → α}
    (hinj : Set.InjOn f S) (hmaps : ∀ x ∈ S, f x ∈ S) :
    ∀ (k : ℕ), ∀ x ∈ S, ∀ y ∈ S, f^[k] x = f^[k] y → x = y
  | 0, _, _, _, _, heq => heq
  | k + 1, x, hx, y, hy, heq => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at heq
    have hfx_eq : f x = f y :=
      injOn_iterate_of_mapsTo hinj hmaps k (f x) (hmaps x hx) (f y) (hmaps y hy) heq
    exact hinj hx hy hfx_eq

private lemma iterate_mem_of_mapsTo {α : Type*} {S : Finset α} {f : α → α}
    (hmaps : ∀ x ∈ S, f x ∈ S) {x₀ : α} (hx₀ : x₀ ∈ S) :
    ∀ i : ℕ, f^[i] x₀ ∈ S
  | 0 => hx₀
  | i + 1 => by
    rw [Function.iterate_succ_apply']
    exact hmaps (f^[i] x₀) (iterate_mem_of_mapsTo hmaps hx₀ i)

/-- If `f` maps a finite set `S` injectively into itself and every positive return period
`f^[m] x = x` (`1 ≤ m`) of every `x ∈ S` is divisible by `L`, then `L ∣ S.card`. -/
private lemma dvd_card_of_injOn_mapsTo_period_dvd {α : Type*} [DecidableEq α]
    {f : α → α} {L : ℕ} :
    ∀ (n : ℕ) (S : Finset α),
      S.card = n →
      Set.InjOn f S →
      (∀ x ∈ S, f x ∈ S) →
      (∀ x ∈ S, ∀ m : ℕ, 1 ≤ m → f^[m] x = x → L ∣ m) →
      L ∣ S.card := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro S hcard hinj hmaps hper
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · rw [hcard]
    exact dvd_zero L
  · obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have hmem : ∀ i : ℕ, f^[i] x₀ ∈ S := iterate_mem_of_mapsTo hmaps hx₀
    have hcancel : ∀ {i j : ℕ}, i < j → f^[i] x₀ = f^[j] x₀ → f^[j - i] x₀ = x₀ := by
      intro i j hlt heq
      have hj_split : j = i + (j - i) := (Nat.add_sub_of_le (le_of_lt hlt)).symm
      have heq' : f^[i] (f^[j - i] x₀) = f^[i] x₀ := by
        rw [← Function.iterate_add_apply, ← hj_split]
        exact heq.symm
      exact injOn_iterate_of_mapsTo hinj hmaps i (f^[j - i] x₀) (hmem (j - i)) x₀ hx₀ heq'
    have hex : ∃ m : ℕ, 1 ≤ m ∧ f^[m] x₀ = x₀ := by
      by_contra hno
      push Not at hno
      have hinj_seq : Set.InjOn (fun i : ℕ ↦ f^[i] x₀) (Finset.range (n + 1)) := by
        intro i _ j _ heq
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact hno (j - i) (by omega) (hcancel hlt heq)
        · exact hno (i - j) (by omega) (hcancel hgt heq.symm)
      have himg_sub : (Finset.range (n + 1)).image (fun i : ℕ ↦ f^[i] x₀) ⊆ S := by
        intro y hy
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
        exact hmem i
      have hle_card : ((Finset.range (n + 1)).image (fun i : ℕ ↦ f^[i] x₀)).card ≤ S.card :=
        Finset.card_le_card himg_sub
      rw [Finset.card_image_of_injOn hinj_seq, Finset.card_range, hcard] at hle_card
      omega
    classical
    let m₀ : ℕ := Nat.find hex
    have hm₀_spec : 1 ≤ m₀ ∧ f^[m₀] x₀ = x₀ := Nat.find_spec hex
    have hm₀_min : ∀ m < m₀, ¬ (1 ≤ m ∧ f^[m] x₀ = x₀) := fun m hm ↦ Nat.find_min hex hm
    have hL_m₀ : L ∣ m₀ := hper x₀ hx₀ m₀ hm₀_spec.1 hm₀_spec.2
    let O : Finset α := (Finset.range m₀).image (fun i : ℕ ↦ f^[i] x₀)
    have hO_sub : O ⊆ S := by
      intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact hmem i
    have hO_inj : Set.InjOn (fun i : ℕ ↦ f^[i] x₀) (Finset.range m₀) := by
      intro i hi j hj heq
      have hi_lt : i < m₀ := Finset.mem_range.mp hi
      have hj_lt : j < m₀ := Finset.mem_range.mp hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hm₀_min (j - i) (by omega) ⟨by omega, hcancel hlt heq⟩
      · exact hm₀_min (i - j) (by omega) ⟨by omega, hcancel hgt heq.symm⟩
    have hO_card : O.card = m₀ := by
      dsimp only [O]
      rw [Finset.card_image_of_injOn hO_inj, Finset.card_range]
    have hO_maps : ∀ y ∈ O, f y ∈ O := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      have hi_lt : i < m₀ := Finset.mem_range.mp hi
      rw [← Function.iterate_succ_apply' f i x₀]
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi_lt) with hlt1 | heq1
      · exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr hlt1, rfl⟩
      · rw [heq1, hm₀_spec.2]
        exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
    have hO_img : O.image f = O := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
        exact hO_maps y hy
      · rw [Finset.card_image_of_injOn (hinj.mono hO_sub)]
    let S_rem : Finset α := S \ O
    have hS_rem_sub : S_rem ⊆ S := Finset.sdiff_subset
    have hcard_split : S_rem.card + O.card = S.card := Finset.card_sdiff_add_card_eq_card hO_sub
    have hS_rem_lt : S_rem.card < n := by omega
    have hS_rem_maps : ∀ z ∈ S_rem, f z ∈ S_rem := by
      intro z hz
      obtain ⟨hzS, hzO⟩ := Finset.mem_sdiff.mp hz
      refine Finset.mem_sdiff.mpr ⟨hmaps z hzS, fun hfzO ↦ ?_⟩
      rw [← hO_img] at hfzO
      obtain ⟨y, hyO, hfy⟩ := Finset.mem_image.mp hfzO
      have hyz : y = z := hinj (hO_sub hyO) hzS hfy
      exact hzO (hyz ▸ hyO)
    have hL_rem : L ∣ S_rem.card :=
      ih S_rem.card hS_rem_lt S_rem rfl (hinj.mono hS_rem_sub)
        hS_rem_maps (fun z hz ↦ hper z (hS_rem_sub hz))
    rw [← hcard_split, hO_card]
    exact dvd_add hL_rem hL_m₀

/-! ## Part 3: General Finite-Field Kummer Prime-Quotient Frobenius Orbit-Size Theorem -/

private def frobPow (R : Type*) [CommSemiring R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    ℕ → (R →+* R)
  | 0 => RingHom.id R
  | j + 1 => (frobenius R p).comp (frobPow R p j)

private lemma frobPow_apply {R : Type*} [CommSemiring R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (j : ℕ) (x : R) :
    frobPow R p j x = x ^ (p ^ j) := by
  induction j with
  | zero => simp [frobPow]
  | succ j ih =>
    change (frobPow R p j x) ^ p = x ^ (p ^ (j + 1))
    rw [ih, ← pow_mul, pow_succ]

private lemma frobPow_iterate_apply {R : Type*} [CommSemiring R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (s : ℕ) (x : R) :
    ∀ m : ℕ, (frobPow R p s)^[m] x = x ^ ((p ^ s) ^ m)
  | 0 => by simp
  | m + 1 => by
    rw [Function.iterate_succ_apply', frobPow_apply, frobPow_iterate_apply p s x m,
      ← pow_mul, ← pow_succ]

private lemma separable_X_pow_sub_C {E : Type*} [Field E] {e : ℕ} (he_pos : 1 ≤ e)
    (he_ne : (e : E) ≠ 0) {δ : E} (hδ_ne : δ ≠ 0) :
    ((X : E[X]) ^ e - Polynomial.C δ).Separable := by
  unfold Polynomial.Separable
  have he1 : (e - 1) + 1 = e := by omega
  have hder : ((X : E[X]) ^ e - Polynomial.C δ).derivative = Polynomial.C (e : E) * X ^ (e - 1) := by
    rw [← he1, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
      sub_zero, Nat.add_sub_cancel, he1]
  rw [hder]
  refine ⟨Polynomial.C (-δ⁻¹), Polynomial.C (δ⁻¹ * (e : E)⁻¹) * X, ?_⟩
  have hXpow : (X : E[X]) * X ^ (e - 1) = X ^ e := by
    conv_rhs => rw [← he1, pow_succ']
  have h1 : Polynomial.C (-δ⁻¹) * ((X : E[X]) ^ e - Polynomial.C δ) =
      - (Polynomial.C δ⁻¹ * X ^ e) + 1 := by
    rw [mul_sub, ← map_mul, neg_mul, inv_mul_cancel₀ hδ_ne]
    simp only [map_neg, map_one, neg_mul, sub_neg_eq_add]
  have h2 : Polynomial.C (δ⁻¹ * (e : E)⁻¹) * X * (Polynomial.C (e : E) * X ^ (e - 1)) =
      Polynomial.C δ⁻¹ * X ^ e := by
    calc Polynomial.C (δ⁻¹ * (e : E)⁻¹) * X * (Polynomial.C (e : E) * X ^ (e - 1))
        = (Polynomial.C (δ⁻¹ * (e : E)⁻¹) * Polynomial.C (e : E)) * (X * X ^ (e - 1)) := by ring
      _ = Polynomial.C (δ⁻¹ * ((e : E)⁻¹ * (e : E))) * X ^ e := by
          rw [← map_mul, mul_assoc, hXpow]
      _ = Polynomial.C δ⁻¹ * X ^ e := by rw [inv_mul_cancel₀ he_ne, mul_one]
  rw [h1, h2]
  ring

private lemma nat_sub_one_dvd_pow_sub_one (B : ℕ) (hB : 1 ≤ B) :
    ∀ t : ℕ, (B - 1) ∣ (B ^ t - 1)
  | 0 => by simp
  | t + 1 => by
    obtain ⟨c, hc⟩ := nat_sub_one_dvd_pow_sub_one B hB t
    have hBt_pos : 1 ≤ B ^ t := Nat.one_le_pow t B hB
    refine ⟨B * c + 1, ?_⟩
    have hsplit : B ^ (t + 1) - 1 = B * (B ^ t - 1) + (B - 1) := by
      rw [pow_succ']
      zify [hB, hBt_pos, Nat.mul_pos hB hBt_pos]
      ring
    rw [hsplit, hc]
    ring

private lemma bezout_mul_eq_mul_add_one {q N : ℕ} (hq : 2 ≤ q) (hN : 1 ≤ N)
    (hcop : Nat.Coprime q N) :
    ∃ u v : ℕ, q * u = N * v + 1 := by
  rcases eq_or_lt_of_le hN with hN1 | hN2
  · refine ⟨1, q - 1, ?_⟩
    rw [← hN1]
    omega
  · have hbez : (1 : ℤ) = (q : ℤ) * Nat.gcdA q N + (N : ℤ) * Nat.gcdB q N := by
      have hg := Nat.gcd_eq_gcd_ab q N
      rw [hcop.gcd_eq_one, Nat.cast_one] at hg
      exact hg
    have hN_pos : (0 : ℤ) < (N : ℤ) := by positivity
    let u_int : ℤ := Nat.gcdA q N % (N : ℤ)
    have hu_nonneg : 0 ≤ u_int := Int.emod_nonneg _ (ne_of_gt hN_pos)
    let u : ℕ := u_int.toNat
    have hu_cast : (u : ℤ) = u_int := Int.toNat_of_nonneg hu_nonneg
    have hdvd_int : (N : ℤ) ∣ ((q : ℤ) * (u : ℤ) - 1) := by
      refine ⟨-Nat.gcdB q N - (q : ℤ) * (Nat.gcdA q N / (N : ℤ)), ?_⟩
      have hmod_def : u_int = Nat.gcdA q N - (N : ℤ) * (Nat.gcdA q N / (N : ℤ)) :=
        Int.emod_def (Nat.gcdA q N) (N : ℤ)
      rw [hu_cast, hmod_def]
      linear_combination -hbez
    have hu_pos : 1 ≤ u := by
      by_contra hu0
      have h0 : u = 0 := Nat.eq_zero_of_not_pos hu0
      rw [h0, Nat.cast_zero, mul_zero, zero_sub] at hdvd_int
      have hdvd1 : (N : ℤ) ∣ 1 := dvd_neg.mp hdvd_int
      have hle1 : N ≤ 1 := Int.ofNat_le.mp (Int.le_of_dvd (by decide) hdvd1)
      omega
    have hqu_ge1 : 1 ≤ q * u := Nat.mul_pos (by omega : 0 < q) hu_pos
    have hdvd_nat : N ∣ (q * u - 1) := by
      apply Int.ofNat_dvd.mp
      rw [Nat.cast_sub hqu_ge1, Nat.cast_mul, Nat.cast_one]
      exact hdvd_int
    obtain ⟨v, hv⟩ := hdvd_nat
    exact ⟨u, v, (Nat.sub_eq_iff_eq_add hqu_ge1).mp hv⟩

private lemma eq_one_of_pow_eq_one_of_coprime {E : Type*} [Field E] {ξ : E} (hξ_ne : ξ ≠ 0)
    {a b : ℕ} (hcop : Nat.Coprime a b) (ha : ξ ^ a = 1) (hb : ξ ^ b = 1) :
    ξ = 1 := by
  let u : Eˣ := Units.mk0 ξ hξ_ne
  have hua : u ^ a = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact ha)
  have hub : u ^ b = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hb)
  have hdvd_a : orderOf u ∣ a := orderOf_dvd_iff_pow_eq_one.mpr hua
  have hdvd_b : orderOf u ∣ b := orderOf_dvd_iff_pow_eq_one.mpr hub
  have hdvd_one : orderOf u ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hdvd_a hdvd_b
  have hu1 : u ^ 1 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd_one
  rw [pow_one] at hu1
  exact congrArg Units.val hu1

private lemma kummer_prime_quotient_over_algClosed {F E : Type*} [Field F] [DecidableEq F]
    [Field E] [IsAlgClosed E] [Algebra F E]
    {p s e d q L : ℕ} [Fact p.Prime] [CharP F p]
    (hs_pos : 1 ≤ s) (hF_card : Nat.card F = p ^ s)
    (he_pos : 1 ≤ e) (he_lt_p : e < p)
    (hq_prime : Nat.Prime q) (hq_dvd_e : q ∣ e)
    (hndvd_qF1 : ¬ (q ∣ (p ^ s - 1)))
    (hL_pos : 1 ≤ L)
    (hL_dvd : q ∣ ((p ^ s) ^ L - 1))
    (hL_min : ∀ m : ℕ, 1 ≤ m → m < L → ¬ (q ∣ ((p ^ s) ^ m - 1)))
    {α : F} (hα_ne : α ≠ 0)
    {M : F[X]} (hMm : M.Monic) (hMd : M.natDegree = d)
    (hdvd : M ∣ ((X : F[X]) ^ e - Polynomial.C α)) :
    ∃ r₀ : ℕ, r₀ ≤ e / q ∧ r₀ ≤ d ∧ L ∣ (d - r₀) := by
  classical
  let q_F : ℕ := p ^ s
  have hp_ge2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hqF_ge2 : 2 ≤ q_F := by
    calc 2 ≤ p ^ 1 := by rw [pow_one]; exact hp_ge2
      _ ≤ p ^ s := Nat.pow_le_pow_right (by omega) hs_pos
  have hcard_ne0 : Nat.card F ≠ 0 := by rw [hF_card]; omega
  have : Finite F := Nat.finite_of_card_ne_zero hcard_ne0
  let _ : Fintype F := Fintype.ofFinite F
  have hfintype_card : Fintype.card F = q_F := by rw [Fintype.card_eq_nat_card, hF_card]
  have hunits_card : Fintype.card Fˣ = q_F - 1 := by rw [Fintype.card_units, hfintype_card]
  have hpow_sub_one : ∀ a : F, a ≠ 0 → a ^ (q_F - 1) = 1 := by
    intro a ha
    let u : Fˣ := Units.mk0 a ha
    have hu : u ^ (q_F - 1) = 1 := by rw [← hunits_card]; exact pow_card_eq_one
    have hval := congrArg Units.val hu
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at hval
  have hfermat : ∀ a : F, a ^ q_F = a := by
    intro a
    by_cases ha : a = 0
    · rw [ha, zero_pow (by omega : q_F ≠ 0)]
    · have hexp : (q_F - 1) + 1 = q_F := by omega
      rw [← hexp, pow_succ, hpow_sub_one a ha, one_mul]
  -- Extract `F`-rational `q`-th root `w0_F` of `α` using `Nat.Coprime q (q_F - 1)`
  have hcop_q : Nat.Coprime q (q_F - 1) := hq_prime.coprime_iff_not_dvd.mpr hndvd_qF1
  obtain ⟨u_exp, v_exp, huv⟩ := bezout_mul_eq_mul_add_one hq_prime.two_le (by omega) hcop_q
  let w0_F : F := α ^ u_exp
  have hw0_F_ne : w0_F ≠ 0 := pow_ne_zero u_exp hα_ne
  have hw0_F_pow : w0_F ^ q = α := by
    dsimp only [w0_F]
    rw [← pow_mul, mul_comm u_exp q, huv, pow_add, pow_one, pow_mul,
      hpow_sub_one α hα_ne, one_pow, one_mul]
  -- Lift to `E`
  have : CharP E p := (Algebra.charP_iff F E p).mp inferInstance
  let φ : F →+* E := algebraMap F E
  let σ : E →+* E := frobPow E p s
  have hσ_inj : Function.Injective σ := σ.injective
  have hσ_fix_F : ∀ a : F, σ (φ a) = φ a := by
    intro a
    rw [frobPow_apply]
    change (φ a) ^ q_F = φ a
    rw [← map_pow, hfermat a]
  let α_E : E := φ α
  let w0 : E := φ w0_F
  have hα_E_ne : α_E ≠ 0 := fun h0 ↦ hα_ne (φ.injective (by rw [map_zero]; exact h0))
  have hw0_ne : w0 ≠ 0 := fun h0 ↦ hw0_F_ne (φ.injective (by rw [map_zero]; exact h0))
  have hw0_pow_q : w0 ^ q = α_E := by dsimp only [w0, α_E]; rw [← map_pow, hw0_F_pow]
  have hσ_w0 : σ w0 = w0 := hσ_fix_F w0_F
  have hσ_iter_w0 : ∀ m : ℕ, σ^[m] w0 = w0 := fun m ↦ by
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, hσ_w0]
  have he_E_ne : (e : E) ≠ 0 := by
    intro he0
    have hdvd_pe : p ∣ e := (CharP.cast_eq_zero_iff E p e).mp he0
    have hle := Nat.le_of_dvd he_pos hdvd_pe
    omega
  -- Lift `M` to `M_E := M.map φ`
  let M_E : E[X] := M.map φ
  have hM_Em : M_E.Monic := hMm.map φ
  have hM_Ed : M_E.natDegree = d := (hMm.natDegree_map φ).trans hMd
  have hdvd_E : M_E ∣ ((X : E[X]) ^ e - Polynomial.C α_E) := by
    obtain ⟨U_M, hUM⟩ := hdvd
    refine ⟨U_M.map φ, ?_⟩
    have hm := congrArg (Polynomial.map φ) hUM
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_mul] at hm
    exact hm
  have hsep_M : M_E.Separable :=
    (separable_X_pow_sub_C he_pos he_E_ne hα_E_ne).of_dvd hdvd_E
  have hnup : M_E.roots.Nodup := Polynomial.nodup_roots hsep_M
  have hsplits : M_E.Splits := IsAlgClosed.splits M_E
  let R_M : Finset E := M_E.roots.toFinset
  have hRM_card : R_M.card = d := by
    dsimp only [R_M]
    rw [Multiset.toFinset_card_of_nodup hnup, ← hsplits.natDegree_eq_card_roots, hM_Ed]
  have hRM_pow : ∀ z ∈ R_M, z ^ e = α_E := by
    intro z hz
    have hz_root : M_E.eval z = 0 :=
      (Polynomial.mem_roots hM_Em.ne_zero).mp (Multiset.mem_toFinset.mp hz)
    obtain ⟨U_E, hUE⟩ := hdvd_E
    have hev := congrArg (fun T : E[X] ↦ T.eval z) hUE
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_mul, hz_root, zero_mul] at hev
    exact sub_eq_zero.mp hev
  have hRM_ne : ∀ z ∈ R_M, z ≠ 0 := by
    intro z hz h0
    have hpe := hRM_pow z hz
    rw [h0, zero_pow (by omega : e ≠ 0)] at hpe
    exact hα_E_ne hpe.symm
  have hME_map_σ : M_E.map σ = M_E := by
    dsimp only [M_E]
    rw [Polynomial.map_map]
    congr 1
    ext a
    exact hσ_fix_F a
  have hRM_maps_σ : ∀ z ∈ R_M, σ z ∈ R_M := by
    intro z hz
    have hz_root : M_E.eval z = 0 :=
      (Polynomial.mem_roots hM_Em.ne_zero).mp (Multiset.mem_toFinset.mp hz)
    have hhom := Polynomial.hom_eval₂ M_E (RingHom.id E) σ z
    simp only [RingHom.comp_id] at hhom
    have hσz_root : M_E.eval (σ z) = 0 := by
      conv_lhs => rw [← hME_map_σ]
      rw [Polynomial.eval_map, ← hhom]
      exact (congrArg σ hz_root).trans (map_zero σ)
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hM_Em.ne_zero).mpr hσz_root)
  -- Partition `R_M` into `R_fix` (`z ^ g0 = w0`) and `R_orb := R_M \ R_fix`
  let g0 : ℕ := e / q
  have hg0_mul : g0 * q = e := Nat.div_mul_cancel hq_dvd_e
  have hg0_pos : 1 ≤ g0 := by
    by_contra hg0_0
    have h0 : g0 = 0 := Nat.eq_zero_of_not_pos hg0_0
    rw [h0, zero_mul] at hg0_mul
    omega
  let R_fix : Finset E := R_M.filter (fun z ↦ z ^ g0 = w0)
  let R_orb : Finset E := R_M \ R_fix
  have hR_fix_sub : R_fix ⊆ R_M := Finset.filter_subset _ _
  have hR_orb_sub : R_orb ⊆ R_M := Finset.sdiff_subset
  have hcard_sum : R_orb.card + R_fix.card = d := by
    rw [Finset.card_sdiff_add_card_eq_card hR_fix_sub, hRM_card]
  have hR_fix_le : R_fix.card ≤ g0 := by
    let P_fix : E[X] := (X : E[X]) ^ g0 - Polynomial.C w0
    have hP_fix_monic : P_fix.Monic := Polynomial.monic_X_pow_sub_C w0 (by omega : g0 ≠ 0)
    have hP_fix_deg : P_fix.natDegree = g0 := Polynomial.natDegree_X_pow_sub_C
    have hsub_roots : R_fix ⊆ P_fix.roots.toFinset := by
      intro z hz
      obtain ⟨_, hzg0⟩ := Finset.mem_filter.mp hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_fix_monic.ne_zero, Polynomial.IsRoot.def]
      dsimp only [P_fix]
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        hzg0, sub_self]
    calc R_fix.card
        ≤ P_fix.roots.toFinset.card := Finset.card_le_card hsub_roots
      _ ≤ P_fix.roots.card := Multiset.toFinset_card_le _
      _ ≤ P_fix.natDegree := Polynomial.card_roots' P_fix
      _ = g0 := hP_fix_deg
  -- Prove `σ` maps `R_orb` into `R_orb` and every return period on `R_orb` is divisible by `L`
  have hR_orb_maps : ∀ z ∈ R_orb, σ z ∈ R_orb := by
    intro z hz
    obtain ⟨hzM, hz_nfix⟩ := Finset.mem_sdiff.mp hz
    have hzg0_ne : z ^ g0 ≠ w0 := fun heq ↦ hz_nfix (Finset.mem_filter.mpr ⟨hzM, heq⟩)
    refine Finset.mem_sdiff.mpr ⟨hRM_maps_σ z hzM, fun hσ_fix ↦ ?_⟩
    obtain ⟨_, hσ_eq⟩ := Finset.mem_filter.mp hσ_fix
    rw [← map_pow σ z g0, ← hσ_w0] at hσ_eq
    exact hzg0_ne (hσ_inj hσ_eq)
  have hR_orb_period : ∀ z ∈ R_orb, ∀ m : ℕ, 1 ≤ m → σ^[m] z = z → L ∣ m := by
    intro z hz m hm_pos hzm
    obtain ⟨hzM, hz_nfix⟩ := Finset.mem_sdiff.mp hz
    have hzg0_ne : z ^ g0 ≠ w0 := fun heq ↦ hz_nfix (Finset.mem_filter.mpr ⟨hzM, heq⟩)
    have hz_ne : z ≠ 0 := hRM_ne z hzM
    let w : E := z ^ g0
    let ξ : E := w * w0⁻¹
    have hw_ne : w ≠ 0 := pow_ne_zero g0 hz_ne
    have hξ_ne : ξ ≠ 0 := mul_ne_zero hw_ne (inv_ne_zero hw0_ne)
    have hξ_ne_one : ξ ≠ 1 := by
      intro h1
      dsimp only [ξ] at h1
      have hw_eq : w = w0 := by
        calc w = (w * w0⁻¹) * w0 := by rw [mul_assoc, inv_mul_cancel₀ hw0_ne, mul_one]
          _ = 1 * w0 := by rw [h1]
          _ = w0 := one_mul w0
      exact hzg0_ne hw_eq
    have hw_pow_q : w ^ q = α_E := by
      dsimp only [w]
      rw [← pow_mul, hg0_mul]
      exact hRM_pow z hzM
    have hξ_pow_q : ξ ^ q = 1 := by
      dsimp only [ξ]
      rw [mul_pow, inv_pow, hw_pow_q, hw0_pow_q, mul_inv_cancel₀ hα_E_ne]
    have hz_pow_qFm : z ^ (q_F ^ m) = z := by
      rw [← frobPow_iterate_apply p s z m]
      exact hzm
    have hw0_pow_qFm : w0 ^ (q_F ^ m) = w0 := by
      rw [← frobPow_iterate_apply p s w0 m]
      exact hσ_iter_w0 m
    have hw_pow_qFm : w ^ (q_F ^ m) = w := by
      dsimp only [w]
      rw [pow_right_comm, hz_pow_qFm]
    have hξ_pow_qFm : ξ ^ (q_F ^ m) = ξ := by
      dsimp only [ξ]
      rw [mul_pow, inv_pow, hw_pow_qFm, hw0_pow_qFm]
    have hqFm_ge2 : 2 ≤ q_F ^ m := by
      calc 2 ≤ q_F ^ 1 := by rw [pow_one]; exact hqF_ge2
        _ ≤ q_F ^ m := Nat.pow_le_pow_right (by omega) hm_pos
    have hξ_pow_sub1 : ξ ^ (q_F ^ m - 1) = 1 := by
      apply mul_right_cancel₀ hξ_ne
      calc ξ ^ (q_F ^ m - 1) * ξ
          = ξ ^ ((q_F ^ m - 1) + 1) := (pow_succ ξ (q_F ^ m - 1)).symm
        _ = ξ ^ (q_F ^ m) := by rw [show (q_F ^ m - 1) + 1 = q_F ^ m by omega]
        _ = 1 * ξ := by rw [hξ_pow_qFm, one_mul]
    have hq_dvd_qFm1 : q ∣ (q_F ^ m - 1) := by
      by_contra hndvd_m
      have hcop_m : Nat.Coprime q (q_F ^ m - 1) := hq_prime.coprime_iff_not_dvd.mpr hndvd_m
      exact hξ_ne_one (eq_one_of_pow_eq_one_of_coprime hξ_ne hcop_m hξ_pow_q hξ_pow_sub1)
    -- Deduce `L ∣ m` from `q ∣ (q_F ^ m - 1)`, `q ∣ (q_F ^ L - 1)`, and `hL_min`
    have hrem_zero : m % L = 0 := by
      by_contra hrem_ne
      have hrem_pos : 1 ≤ m % L := Nat.pos_of_ne_zero hrem_ne
      have hrem_lt : m % L < L := Nat.mod_lt m hL_pos
      have hdvd_mult : q ∣ (q_F ^ (L * (m / L)) - 1) := by
        rw [pow_mul]
        exact dvd_trans hL_dvd
          (nat_sub_one_dvd_pow_sub_one (q_F ^ L) (Nat.one_le_pow L q_F (by omega)) (m / L))
      have hm_div : L * (m / L) + m % L = m := Nat.div_add_mod m L
      have hpow_id :
          (q_F ^ (m % L) - 1) + q_F ^ (m % L) * (q_F ^ (L * (m / L)) - 1) = q_F ^ m - 1 := by
        have h1 : 1 ≤ q_F ^ (m % L) := Nat.one_le_pow _ _ (by omega)
        have h2 : 1 ≤ q_F ^ (L * (m / L)) := Nat.one_le_pow _ _ (by omega)
        have hprod : q_F ^ (m % L) * q_F ^ (L * (m / L)) = q_F ^ m := by
          conv_rhs => rw [← hm_div, pow_add, mul_comm]
        have hle_prod : q_F ^ (m % L) ≤ q_F ^ m := by
          rw [← hprod]
          exact Nat.le_mul_of_pos_right _ h2
        rw [Nat.mul_sub_one, hprod, Nat.add_comm, Nat.sub_add_sub_cancel hle_prod h1]
      have hdvd_rem : q ∣ (q_F ^ (m % L) - 1) :=
        (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right hdvd_mult _)).mpr
          (by rw [hpow_id]; exact hq_dvd_qFm1)
      exact hL_min (m % L) hrem_pos hrem_lt hdvd_rem
    exact Nat.dvd_of_mod_eq_zero hrem_zero
  have hL_orb : L ∣ R_orb.card :=
    dvd_card_of_injOn_mapsTo_period_dvd R_orb.card R_orb rfl hσ_inj.injOn hR_orb_maps hR_orb_period
  refine ⟨R_fix.card, hR_fix_le, by omega, ?_⟩
  have hdiff_eq : d - R_fix.card = R_orb.card := by omega
  rwa [hdiff_eq]

/-- **General Finite-Field Kummer Prime-Quotient Frobenius Orbit-Size Theorem:**
Over any finite field `F` of characteristic `p` and cardinality `Nat.card F = p ^ s` (`1 ≤ s`),
let `M : F[X]` be monic of degree `d` dividing `X ^ e - C α` (`α ≠ 0`, `1 ≤ e`, `e < p`).
If `q` is a prime dividing `e` with `¬ (q ∣ (p ^ s - 1))`, `L ≥ 1` is the multiplicative order of
`p ^ s` modulo `q`, and `e / q < L`, then **`d % L ≤ e / q`**. -/
theorem kummer_prime_quotient_frobenius_orbit_remainder {F : Type*} [Field F] [DecidableEq F]
    {p s e d q L : ℕ} [Fact p.Prime] [CharP F p]
    (hs_pos : 1 ≤ s) (hF_card : Nat.card F = p ^ s)
    (he_pos : 1 ≤ e) (he_lt_p : e < p)
    (hq_prime : Nat.Prime q) (hq_dvd_e : q ∣ e)
    (hndvd_qF1 : ¬ (q ∣ (p ^ s - 1)))
    (hL_pos : 1 ≤ L)
    (hL_dvd : q ∣ ((p ^ s) ^ L - 1))
    (hL_min : ∀ m : ℕ, 1 ≤ m → m < L → ¬ (q ∣ ((p ^ s) ^ m - 1)))
    (heq_lt_L : e / q < L)
    {α : F} (hα_ne : α ≠ 0)
    {M : F[X]} (hMm : M.Monic) (hMd : M.natDegree = d)
    (hdvd : M ∣ ((X : F[X]) ^ e - Polynomial.C α)) :
    d % L ≤ e / q := by
  obtain ⟨r₀, hr₀_le_eq, hr₀_le_d, hL_dvd_diff⟩ :=
    kummer_prime_quotient_over_algClosed (E := AlgebraicClosure F)
      hs_pos hF_card he_pos he_lt_p hq_prime hq_dvd_e hndvd_qF1 hL_pos hL_dvd hL_min
      hα_ne hMm hMd hdvd
  obtain ⟨Q_orb, hQ_orb⟩ := hL_dvd_diff
  have hd_eq : d = L * Q_orb + r₀ := by omega
  have hr₀_lt_L : r₀ < L := lt_of_le_of_lt hr₀_le_eq heq_lt_L
  rw [hd_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hr₀_lt_L]
  exact hr₀_le_eq

/-! ## Part 4: Two-Fibre Boundary Cubic Obstruction (`@rukafe0x` Result 15 `M-0966`) -/

/-- **Two-Fibre Prime-Quotient Orbit-Size Obstruction (`lemma_m31_orbit_size_cubic_obstruction`):**
Over any finite field `F` of cardinality `Nat.card F = p ^ 2` (`p` prime, `4 * h < p`), at the
Wronskian boundary `e = 2 * h + 2 * k`, `f = 2 * h - 2 * k` (`1 ≤ k`, `2 * k + 1 ≤ h`,
`¬ (3 ∣ e)`), if a prime `q ∣ e` satisfies `¬ (q ∣ (p ^ 2 - 1))` and `L ≥ 1` is the multiplicative
order of `p ^ 2` modulo `q` with `e / q < L` and `e / q < h % L ∨ e / q < (2 * k) % L`, then NO
polynomials `(A, B, Q)` can satisfy `A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q`! -/
theorem lemma_m31_orbit_size_cubic_obstruction {F : Type*} [Field F] [DecidableEq F]
    {p q L : ℕ} [Fact p.Prime] [CharP F p]
    (hF_card : Nat.card F = p ^ 2)
    {A B Q : F[X]} {h k e f : ℕ}
    (hk_pos : 1 ≤ k) (h2k_lt : 2 * k + 1 ≤ h)
    (he_eq : e = 2 * h + 2 * k) (hf_eq : f = 2 * h - 2 * k)
    (hndvd3 : ¬ (3 ∣ e))
    (hp_gt : 4 * h < p)
    (hq_prime : Nat.Prime q) (hq_dvd_e : q ∣ e)
    (hndvd_p2_sub1 : ¬ (q ∣ (p ^ 2 - 1)))
    (hL_pos : 1 ≤ L)
    (hL_dvd : q ∣ ((p ^ 2) ^ L - 1))
    (hL_min : ∀ m : ℕ, 1 ≤ m → m < L → ¬ (q ∣ ((p ^ 2) ^ m - 1)))
    (heq_lt_L : e / q < L)
    (horbit_fail : e / q < h % L ∨ e / q < (2 * k) % L)
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hQd : Q ≠ 0 → Q.natDegree + f ≤ 2 * h)
    (hident : A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q) :
    False := by
  have hrchar : ringChar F = p := ringChar.eq F p
  obtain ⟨_, Q₁, ρ, _, _, _, hQ₁m, hQ₁d, hρ_ne, _, hdvd_A, _, hdvd_Q₁, _⟩ :=
    all_three_kummer_fibres_of_boundary_cubic hk_pos h2k_lt he_eq hf_eq hndvd3
      (Or.inr (by rw [hrchar]; exact hp_gt)) hAm hAd hBd hB0 hQd hident
  have h3_ne : (3 : F) ≠ 0 := by
    intro h30
    have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff F p 3).mp (by simpa using h30)
    have hle := Nat.le_of_dvd (by decide) hdvd
    omega
  have hneg3ρ_ne : (-3 : F) * ρ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h3_ne) hρ_ne
  have he_pos : 1 ≤ e := by omega
  have he_lt_p : e < p := by omega
  rcases horbit_fail with hh_gt | h2k_gt
  · have hh_le : h % L ≤ e / q :=
      kummer_prime_quotient_frobenius_orbit_remainder (by decide : 1 ≤ 2) hF_card
        he_pos he_lt_p hq_prime hq_dvd_e hndvd_p2_sub1 hL_pos hL_dvd hL_min heq_lt_L
        hneg3ρ_ne hAm hAd hdvd_A
    omega
  · have h2k_le : (2 * k) % L ≤ e / q :=
      kummer_prime_quotient_frobenius_orbit_remainder (by decide : 1 ≤ 2) hF_card
        he_pos he_lt_p hq_prime hq_dvd_e hndvd_p2_sub1 hL_pos hL_dvd hL_min heq_lt_L
        hρ_ne hQ₁m hQ₁d hdvd_Q₁
    omega

/-! ## Part 5: All-Dyadic `5 ≤ r ≤ 31` Vanishing, Composable Reduction, & 11 Concrete Corollaries -/

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

/-- Predicate witnessing that `(e, h, k)` is obstructed over M31 (`Nat.card F = (2 ^ 31 - 1) ^ 2`)
by a prime divisor `q ∣ e` whose quotient `(p ^ 2)`-Frobenius orbit order `L` exceeds `e / q` and
leaves remainder `> e / q` on `h` or `2 * k`. -/
def HasM31PrimeQuotientOrbitObstruction (e h k : ℕ) : Prop :=
  ∃ q L : ℕ,
    Nat.Prime q ∧
    q ∣ e ∧
    ¬ (q ∣ ((2 ^ 31 - 1) ^ 2 - 1)) ∧
    1 ≤ L ∧
    q ∣ (((2 ^ 31 - 1) ^ 2) ^ L - 1) ∧
    (∀ m : ℕ, 1 ≤ m → m < L → ¬ (q ∣ (((2 ^ 31 - 1) ^ 2) ^ m - 1))) ∧
    e / q < L ∧
    (e / q < h % L ∨ e / q < (2 * k) % L)

/-- **All-Dyadic M31 Orbit-Size Inner-Band Vanishing (`m = 5 * 2 ^ (r - 3) + δ`):**
Across every dyadic `5 ≤ r ≤ 31` (`q_oct = 2 ^ (r - 3)`), at `4 * h = 3 * q_oct - δ` (`h ≤ δ`,
`q_oct + h < 3 * δ`), whenever `HasM31PrimeQuotientOrbitObstruction (3 * δ - q_oct) h
(h - 2 * (q_oct - δ))` holds, NO degree-`≤ 2 ^ (r - 1)` polynomial agrees with
`C a * X ^ (5 * q_oct + δ) + R` on `(5 * q_oct + δ) - h` points of `D`, and `NativeListBound = 0`. -/
theorem ambient_and_native_vanishing_m31_orbit_size_inner
    {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    (horbit : HasM31PrimeQuotientOrbitObstruction
      (3 * δ - 2 ^ (r - 3)) h (h - 2 * (2 ^ (r - 3) - δ)))
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
        · obtain ⟨q_pr, L_ord, hqp, hq_dvd, hq_ndvd_p2, hL_pos, hL_dvd, hL_min, heq_lt_L, hfail⟩ :=
            horbit
          let k : ℕ := h' - 2 * (q_oct - δ)
          exact lemma_m31_orbit_size_cubic_obstruction (p := 2 ^ 31 - 1) (q := q_pr) (L := L_ord)
            hF
            (k := k)
            (by omega : 1 ≤ k)
            (by omega : 2 * k + 1 ≤ h')
            (by omega : 3 * δ - q_oct = 2 * h' + 2 * k)
            (by omega : 4 * (q_oct - δ) = 2 * h' - 2 * k)
            hndvd
            (by omega : 4 * h' < 2 ^ 31 - 1)
            hqp hq_dvd hq_ndvd_p2 hL_pos hL_dvd hL_min heq_lt_L hfail
            hAm hAd hBd hB0 hQd hident
      refine ⟨hno_amb, fun L hL ↦ ?_⟩
      have hL_empty : L = ∅ := by
        by_contra hne
        obtain ⟨P, hP_mem⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        obtain ⟨hP_nat, hP_ag⟩ := hL P hP_mem
        exact hno_amb ⟨P, hP_nat.1, hP_ag⟩
      rw [hL_empty, Finset.card_empty, Nat.cast_zero]

/-- **Mirror Duality (`m = 7 * 2 ^ (r - 3) - δ`) at `4 * h = 3 * 2 ^ (r - 3) - δ`:**
Extends `ambient_and_native_vanishing_m31_orbit_size_inner` to `m = 7 * 2 ^ (r - 3) - δ` via
Mersenne circle Frobenius inversion `x ^ p = x⁻¹` (`p = 2 ^ 31 - 1`). -/
theorem ambient_and_native_vanishing_m31_orbit_size_mirror
    {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    (horbit : HasM31PrimeQuotientOrbitObstruction
      (3 * δ - 2 ^ (r - 3)) h (h - 2 * (2 ^ (r - 3) - δ)))
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
  have hinner := ambient_and_native_vanishing_m31_orbit_size_inner hF hr_lo hr_hi
    hD_card hD_pow hδ_pos hδ_lt hh_le hqh hbdry horbit hap_ne (conjRev R) (hconjRev_deg R)
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

/-- Parameter stratum for M31 prime-quotient Frobenius orbit-size boundary vanishing
(`@rukafe0x` Result 15 `M-0966`): at `4 * u + 5 * δ = 15 * 2 ^ (r - 3)` (`u < 2 * (2 ^ (r - 3) + δ)`),
`HasM31PrimeQuotientOrbitObstruction` holds for `e = 3 * δ - 2 ^ (r - 3)`,
`h = u + δ - 3 * 2 ^ (r - 3)`, and `k = u + 3 * δ - 5 * 2 ^ (r - 3)`. -/
def InSingleM31OrbitSizeBoundaryStratum (r m u : ℕ) : Prop :=
  5 ≤ r ∧
  ∃ δ : ℕ, 1 ≤ δ ∧ δ < 2 ^ (r - 3) ∧
    (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) ∧
    u < 2 * (2 ^ (r - 3) + δ) ∧
    4 * u + 5 * δ = 15 * 2 ^ (r - 3) ∧
    HasM31PrimeQuotientOrbitObstruction
      (3 * δ - 2 ^ (r - 3))
      (u + δ - 3 * 2 ^ (r - 3))
      (u + 3 * δ - 5 * 2 ^ (r - 3))

/-- All-dyadic M31 orbit-size boundary complement-vanishing proposition across `5 ≤ r ≤ 31`. -/
def SingleMonomialM31OrbitSizeBoundaryVanishing.{u} : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 5 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ δ : ℕ, 1 ≤ δ → δ < 2 ^ (r - 3) →
        ∀ m : ℕ, (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) →
          ∀ (γ : F) (U : Finset F),
            U.card < 2 * (2 ^ (r - 3) + δ) →
            4 * U.card + 5 * δ = 15 * 2 ^ (r - 3) →
            HasM31PrimeQuotientOrbitObstruction
              (3 * δ - 2 ^ (r - 3))
              (U.card + δ - 3 * 2 ^ (r - 3))
              (U.card + 3 * δ - 5 * 2 ^ (r - 3)) →
            ¬ IsValidCWComplement D r ((X : F[X]) ^ m) γ U

/-- **Main M31 Orbit-Size Boundary Vanishing Theorem (`singleMonomialM31OrbitSizeBoundaryVanishing`):**
Proves `¬ IsValidCWComplement D r (X ^ m) γ U` across all universes `u` and all dyadic `5 ≤ r ≤ 31`
on every Wronskian-boundary cell obstructed by `HasM31PrimeQuotientOrbitObstruction`. -/
theorem singleMonomialM31OrbitSizeBoundaryVanishing.{u} :
    SingleMonomialM31OrbitSizeBoundaryVanishing.{u} := by
  intro F _ _ hF r hr5 hr_hi D hD_card hD_pow δ hδ1 hδ_lt m hm_eq γ U hu_lt hbdry_u horbit hvalid
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
  have horbit' :
      HasM31PrimeQuotientOrbitObstruction
        (3 * δ - 2 ^ (r - 3)) h (h - 2 * (2 ^ (r - 3) - δ)) := by
    rwa [hk_eq]
  have hS_eq : (5 * 2 ^ (r - 3) + δ) - h = S.card := by omega
  rcases hm_eq with rfl | rfl
  · exact (ambient_and_native_vanishing_m31_orbit_size_inner hF hr5 hr_hi
      hD_card hD_pow hδ1 hδ_lt hh_le hqh hbdry horbit' one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩
  · exact (ambient_and_native_vanishing_m31_orbit_size_mirror hF hr5 hr_hi
      hD_card hD_pow hδ1 hδ_lt hh_le hqh hbdry horbit' one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩

/-- Narrowed single-monomial residual complement bound after eliminating `Theorem W` (`M-0958`),
full `Theorem CW*` (`M-0965`), `Lemma Q'_ℓ` (`M-0970`), AND the M31 prime-quotient Frobenius
orbit-size obstruction (`M-0966`). -/
def SingleMonomialResidualAfterOrbitSizeBound.{u} (K : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 4 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ m : ℕ, 5 * 2 ^ (r - 3) ≤ m → m ≤ 7 * 2 ^ (r - 3) → ∀ γ : F,
        ∀ 𝒰 : Finset (Finset F),
          (∀ U ∈ 𝒰,
            IsValidCWComplement D r ((X : F[X]) ^ m) γ U ∧
            ¬ InSingleWronskianStratum r m U.card ∧
            ¬ InSingleFullFrobeniusBoundaryStratum r m U.card ∧
            ¬ InSingleQPrimeBoundaryStratum r m U.card ∧
            ¬ InSingleM31OrbitSizeBoundaryStratum r m U.card) →
          𝒰.card ≤ K * 2 ^ r

/-- `SingleMonomialResidualAfterOrbitSizeBound K` implies
`SingleMonomialResidualAfterCWStarAndQPrimeBound K`. -/
theorem singleMonomialResidualAfterCWStarAndQPrime_of_after_orbitSize.{u} {K : ℕ}
    (hRem : SingleMonomialResidualAfterOrbitSizeBound.{u} K) :
    SingleMonomialResidualAfterCWStarAndQPrimeBound.{u} K := by
  intro F _ _ hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 h𝒰
  refine hRem F hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 (fun U hUm ↦ ?_)
  obtain ⟨hvalid, hnotW, hnotCWStar, hnotQP⟩ := h𝒰 U hUm
  refine ⟨hvalid, hnotW, hnotCWStar, hnotQP, ?_⟩
  rintro ⟨hr5, δ, hδ1, hδ_lt, hm_eq, hu_lt, hbdry, horbit⟩
  exact singleMonomialM31OrbitSizeBoundaryVanishing F hF r hr5 hr_hi D hD_card hD_pow
    δ hδ1 hδ_lt m hm_eq γ U hu_lt hbdry horbit hvalid

/-- `SingleMonomialResidualAfterOrbitSizeBound K` implies `SingleMonomialNonFrobeniusCWBound K`. -/
theorem singleMonomialNonFrobeniusCWBound_of_after_orbitSize.{u} {K : ℕ}
    (hRem : SingleMonomialResidualAfterOrbitSizeBound.{u} K) :
    SingleMonomialNonFrobeniusCWBound.{u} K :=
  singleMonomialNonFrobeniusCWBound_of_after_qPrime
    (singleMonomialResidualAfterCWStarAndQPrime_of_after_orbitSize hRem)

/-- Reduces `CanonicalInteriorCWBound.{u} K` to `SingleMonomialResidualAfterOrbitSizeBound.{u} K`
and `MultiMonomialCanonicalCWBound.{u} K`. -/
theorem canonicalInteriorCWBound_of_cwStar_qPrime_orbitSize_and_multi_sublemmas.{u} {K : ℕ}
    (hRem : SingleMonomialResidualAfterOrbitSizeBound.{u} K)
    (hMulti : MultiMonomialCanonicalCWBound.{u} K) :
    CanonicalInteriorCWBound.{u} K :=
  canonicalInteriorCWBound_of_cwStar_qPrime_and_multi_sublemmas
    (singleMonomialResidualAfterCWStarAndQPrime_of_after_orbitSize hRem)
    hMulti

/-- **Master `CW*` + `Lemma Q'_ℓ` + M31 Orbit-Size Reduced Theorem (`MCAChallenge.InteriorThree K`):**
Reduces `MCAChallenge.InteriorThree.{u} K` (`1 ≤ K ≤ 2 ^ 20`) across all dyadic `4 ≤ r ≤ 31` directly
to `SingleMonomialResidualAfterOrbitSizeBound.{u} K` and `MultiMonomialCanonicalCWBound.{u} K`. -/
theorem interiorThree_of_cwStar_qPrime_orbitSize_and_multi_sublemmas.{u} {K : ℕ}
    (hK_pos : 1 ≤ K) (hK_cap : K ≤ 2 ^ 20)
    (hRem : SingleMonomialResidualAfterOrbitSizeBound.{u} K)
    (hMulti : MultiMonomialCanonicalCWBound.{u} K) :
    MCAChallenge.InteriorThree.{u} K :=
  interiorThree_of_cwStar_qPrime_and_multi_sublemmas
    hK_pos
    hK_cap
    (singleMonomialResidualAfterCWStarAndQPrime_of_after_orbitSize hRem)
    hMulti

/-- **Unified `NativeListBound = 0` Corollary on All M31 Orbit-Size Boundary Cells:** -/
theorem nativeListBound_zero_m31_orbit_size_boundary {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h m : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    (horbit : HasM31PrimeQuotientOrbitObstruction
      (3 * δ - 2 ^ (r - 3)) h (h - 2 * (2 ^ (r - 3) - δ)))
    (hm_eq : m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1)) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        (5 * 2 ^ (r - 3) + δ) - h ≤
          (D.filter fun x ↦ P.eval x = (Polynomial.C a * X ^ m + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) ((5 * 2 ^ (r - 3) + δ) - h)
      (Polynomial.C a * X ^ m + R) 0 := by
  rcases hm_eq with rfl | rfl
  · exact ambient_and_native_vanishing_m31_orbit_size_inner hF hr_lo hr_hi
      hD_card hD_pow hδ_pos hδ_lt hh_le hqh hbdry horbit ha R hR
  · exact ambient_and_native_vanishing_m31_orbit_size_mirror hF hr_lo hr_hi
      hD_card hD_pow hδ_pos hδ_lt hh_le hqh hbdry horbit ha R hR

/-- Certified wrapper turning `certM31OrbitPrime q L = true` directly into `NativeListBound = 0`. -/
theorem nativeListBound_zero_m31_orbit_size_certified {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h m q L : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    (hcert : certM31OrbitPrime q L = true)
    (hq_dvd : q ∣ (3 * δ - 2 ^ (r - 3)))
    (heq_lt : (3 * δ - 2 ^ (r - 3)) / q < L)
    (hrem_gt : (3 * δ - 2 ^ (r - 3)) / q < h % L ∨
      (3 * δ - 2 ^ (r - 3)) / q < (2 * (h - 2 * (2 ^ (r - 3) - δ))) % L)
    (hm_eq : m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1)) :
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) ((5 * 2 ^ (r - 3) + δ) - h)
      (Polynomial.C a * X ^ m + R) 0 := by
  obtain ⟨hqp, hL1, hndvd1, hdvdL, hminL⟩ := certM31OrbitPrime_sound hcert
  exact (nativeListBound_zero_m31_orbit_size_boundary hF hr_lo hr_hi hD_card hD_pow
    hδ_pos hδ_lt hh_le hqh hbdry
    ⟨q, L, hqp, hq_dvd, hndvd1, hL1, hdvdL, hminL, heq_lt, hrem_gt⟩
    hm_eq ha R hR).2

/-! ### Concrete Kernel-Verified Corollaries at `n = 2048` (`r = 11`) and `n = 4096` (`r = 12`) -/

/-- **`n = 2048` (`r = 11`) Cell `(δ, h) = (196, 143)` (`e = 332 = 4 * 83`, `(q, L) = (83, 41)`):**
Proves `NativeListBound D 1024 1333 (C a * X ^ m + R) 0` for `m ∈ {1476, 1596}`. -/
theorem nativeListBound_zero_r11_orbit_1476_1596 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 2048) (hD_pow : ∀ x ∈ D, x ^ 2048 = 1)
    {m : ℕ} (hm : m = 1476 ∨ m = 1596)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 1024) :
    MCAChallenge.NativeListBound D 1024 1333 (Polynomial.C a * X ^ m + R) 0 :=
  nativeListBound_zero_m31_orbit_size_certified hF (r := 11) (δ := 196) (h := 143) (m := m)
    (q := 83) (L := 41)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨4, by decide⟩ (by decide) (Or.inl (by decide))
    (by omega) ha R (by simpa using hR)

/-- **Non-Frobenius `n = 2048` (`r = 11`) Cell `(δ, h) = (204, 141)` (`e = 356 = 4 * 89`,
`(q, L) = (89, 44)`, `-1 ∉ ⟨p mod 356⟩`):**
Proves `NativeListBound D 1024 1343 (C a * X ^ m + R) 0` for `m ∈ {1484, 1588}`. -/
theorem nativeListBound_zero_r11_orbit_1484_1588 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 2048) (hD_pow : ∀ x ∈ D, x ^ 2048 = 1)
    {m : ℕ} (hm : m = 1484 ∨ m = 1588)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 1024) :
    MCAChallenge.NativeListBound D 1024 1343 (Polynomial.C a * X ^ m + R) 0 :=
  nativeListBound_zero_m31_orbit_size_certified hF (r := 11) (δ := 204) (h := 141) (m := m)
    (q := 89) (L := 44)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨4, by decide⟩ (by decide) (Or.inl (by decide))
    (by omega) ha R (by simpa using hR)

/-- **`n = 2048` (`r = 11`) Cell `(δ, h) = (220, 137)` (`e = 404 = 4 * 101`, `(q, L) = (101, 25)`):**
Proves `NativeListBound D 1024 1363 (C a * X ^ m + R) 0` for `m ∈ {1500, 1572}`. -/
theorem nativeListBound_zero_r11_orbit_1500_1572 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 2048) (hD_pow : ∀ x ∈ D, x ^ 2048 = 1)
    {m : ℕ} (hm : m = 1500 ∨ m = 1572)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 1024) :
    MCAChallenge.NativeListBound D 1024 1363 (Polynomial.C a * X ^ m + R) 0 :=
  nativeListBound_zero_m31_orbit_size_certified hF (r := 11) (δ := 220) (h := 137) (m := m)
    (q := 101) (L := 25)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨4, by decide⟩ (by decide) (Or.inl (by decide))
    (by omega) ha R (by simpa using hR)

/-- **Non-Frobenius `n = 4096` (`r = 12`) Result 15 Cell `(δ, h) = (380, 289)` (`e = 628 = 4 * 157`,
`(q, L) = (157, 39)`, `-1 ∉ ⟨p mod 628⟩`):**
Proves `NativeListBound D 2048 2651 (C a * X ^ m + R) 0` for `m ∈ {2940, 3204}`. -/
theorem nativeListBound_zero_r12_orbit_2940_3204 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 4096) (hD_pow : ∀ x ∈ D, x ^ 4096 = 1)
    {m : ℕ} (hm : m = 2940 ∨ m = 3204)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2048) :
    MCAChallenge.NativeListBound D 2048 2651 (Polynomial.C a * X ^ m + R) 0 :=
  nativeListBound_zero_m31_orbit_size_certified hF (r := 12) (δ := 380) (h := 289) (m := m)
    (q := 157) (L := 39)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨4, by decide⟩ (by decide) (Or.inl (by decide))
    (by omega) ha R (by simpa using hR)

/-- **Non-Frobenius `n = 4096` (`r = 12`) Result 15 Cell `(δ, h) = (388, 287)` (`e = 652 = 4 * 163`,
`(q, L) = (163, 81)`, `-1 ∉ ⟨p mod 652⟩`):**
Proves `NativeListBound D 2048 2661 (C a * X ^ m + R) 0` for `m ∈ {2948, 3196}`. -/
theorem nativeListBound_zero_r12_orbit_2948_3196 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 4096) (hD_pow : ∀ x ∈ D, x ^ 4096 = 1)
    {m : ℕ} (hm : m = 2948 ∨ m = 3196)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2048) :
    MCAChallenge.NativeListBound D 2048 2661 (Polynomial.C a * X ^ m + R) 0 :=
  nativeListBound_zero_m31_orbit_size_certified hF (r := 12) (δ := 388) (h := 287) (m := m)
    (q := 163) (L := 81)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨4, by decide⟩ (by decide) (Or.inl (by decide))
    (by omega) ha R (by simpa using hR)

/-- **`n = 4096` (`r = 12`) Cell `(δ, h) = (392, 286)` (`e = 664 = 8 * 83`, `(q, L) = (83, 41)`):**
Proves `NativeListBound D 2048 2666 (C a * X ^ m + R) 0` for `m ∈ {2952, 3192}`. -/
theorem nativeListBound_zero_r12_orbit_2952_3192 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 4096) (hD_pow : ∀ x ∈ D, x ^ 4096 = 1)
    {m : ℕ} (hm : m = 2952 ∨ m = 3192)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2048) :
    MCAChallenge.NativeListBound D 2048 2666 (Polynomial.C a * X ^ m + R) 0 :=
  nativeListBound_zero_m31_orbit_size_certified hF (r := 12) (δ := 392) (h := 286) (m := m)
    (q := 83) (L := 41)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨8, by decide⟩ (by decide) (Or.inl (by decide))
    (by omega) ha R (by simpa using hR)

/-- **Non-Frobenius `n = 4096` (`r = 12`) Result 15 Cell `(δ, h) = (408, 282)` (`e = 712 = 8 * 89`,
`(q, L) = (89, 44)`, `-1 ∉ ⟨p mod 712⟩`):**
Proves `NativeListBound D 2048 2686 (C a * X ^ m + R) 0` for `m ∈ {2968, 3176}`. -/
theorem nativeListBound_zero_r12_orbit_2968_3176 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 4096) (hD_pow : ∀ x ∈ D, x ^ 4096 = 1)
    {m : ℕ} (hm : m = 2968 ∨ m = 3176)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2048) :
    MCAChallenge.NativeListBound D 2048 2686 (Polynomial.C a * X ^ m + R) 0 :=
  nativeListBound_zero_m31_orbit_size_certified hF (r := 12) (δ := 408) (h := 282) (m := m)
    (q := 89) (L := 44)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨8, by decide⟩ (by decide) (Or.inl (by decide))
    (by omega) ha R (by simpa using hR)

/-- **Non-Frobenius `n = 4096` (`r = 12`) Result 15 Cell `(δ, h) = (412, 281)` (`e = 724 = 4 * 181`,
`(q, L) = (181, 90)`, `-1 ∉ ⟨p mod 724⟩`):**
Proves `NativeListBound D 2048 2691 (C a * X ^ m + R) 0` for `m ∈ {2972, 3172}`. -/
theorem nativeListBound_zero_r12_orbit_2972_3172 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 4096) (hD_pow : ∀ x ∈ D, x ^ 4096 = 1)
    {m : ℕ} (hm : m = 2972 ∨ m = 3172)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2048) :
    MCAChallenge.NativeListBound D 2048 2691 (Polynomial.C a * X ^ m + R) 0 :=
  nativeListBound_zero_m31_orbit_size_certified hF (r := 12) (δ := 412) (h := 281) (m := m)
    (q := 181) (L := 90)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨4, by decide⟩ (by decide) (Or.inl (by decide))
    (by omega) ha R (by simpa using hR)

/-- **Non-Frobenius `n = 4096` (`r = 12`) Result 15 Cell `(δ, h) = (428, 277)` (`e = 772 = 4 * 193`,
`(q, L) = (193, 96)`, `-1 ∉ ⟨p mod 772⟩`):**
Proves `NativeListBound D 2048 2711 (C a * X ^ m + R) 0` for `m ∈ {2988, 3156}`. -/
theorem nativeListBound_zero_r12_orbit_2988_3156 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 4096) (hD_pow : ∀ x ∈ D, x ^ 4096 = 1)
    {m : ℕ} (hm : m = 2988 ∨ m = 3156)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2048) :
    MCAChallenge.NativeListBound D 2048 2711 (Polynomial.C a * X ^ m + R) 0 :=
  nativeListBound_zero_m31_orbit_size_certified hF (r := 12) (δ := 428) (h := 277) (m := m)
    (q := 193) (L := 96)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨4, by decide⟩ (by decide) (Or.inl (by decide))
    (by omega) ha R (by simpa using hR)

/-- **`n = 4096` (`r = 12`) Cell `(δ, h) = (436, 275)` (`e = 796 = 4 * 199`, `(q, L) = (199, 99)`):**
Proves `NativeListBound D 2048 2721 (C a * X ^ m + R) 0` for `m ∈ {2996, 3148}`. -/
theorem nativeListBound_zero_r12_orbit_2996_3148 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 4096) (hD_pow : ∀ x ∈ D, x ^ 4096 = 1)
    {m : ℕ} (hm : m = 2996 ∨ m = 3148)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2048) :
    MCAChallenge.NativeListBound D 2048 2721 (Polynomial.C a * X ^ m + R) 0 :=
  nativeListBound_zero_m31_orbit_size_certified hF (r := 12) (δ := 436) (h := 275) (m := m)
    (q := 199) (L := 99)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨4, by decide⟩ (by decide) (Or.inl (by decide))
    (by omega) ha R (by simpa using hR)

/-- **`n = 4096` (`r = 12`) Cell `(δ, h) = (440, 274)` (`e = 808 = 8 * 101`, `(q, L) = (101, 25)`):**
Proves `NativeListBound D 2048 2726 (C a * X ^ m + R) 0` for `m ∈ {3000, 3144}`. -/
theorem nativeListBound_zero_r12_orbit_3000_3144 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 4096) (hD_pow : ∀ x ∈ D, x ^ 4096 = 1)
    {m : ℕ} (hm : m = 3000 ∨ m = 3144)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2048) :
    MCAChallenge.NativeListBound D 2048 2726 (Polynomial.C a * X ^ m + R) 0 :=
  nativeListBound_zero_m31_orbit_size_certified hF (r := 12) (δ := 440) (h := 274) (m := m)
    (q := 101) (L := 25)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨8, by decide⟩ (by decide) (Or.inl (by decide))
    (by omega) ha R (by simpa using hR)

end InteriorThreeM31OrbitSizeObstruction
