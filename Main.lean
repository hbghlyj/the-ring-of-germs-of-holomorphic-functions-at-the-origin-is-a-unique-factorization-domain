import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 8000000

/-!
# `𝒪ₙ` is a UFD (algebraic core, assuming Weierstrass Preparation)

This file formalizes the *inductive step* of the classical proof that the ring
`𝒪ₙ` of germs of holomorphic functions at the origin of `ℂⁿ` is a unique
factorization domain, **assuming the Weierstrass Preparation Theorem (WPT)**.

The analytic objects `𝒪ₙ` and the WPT itself are not part of `Mathlib`, so we
capture the proof at the level of abstraction that the textbook argument actually
uses.  The data is:

* `R`  — playing the role of `𝒪ₙ₋₁`, assumed a UFD (this is the induction
  hypothesis).  Then `Polynomial R = 𝒪ₙ₋₁[w]` is automatically a UFD, which is
  exactly **Gauss's Lemma** (a `Mathlib` instance).
* `B`  — playing the role of `𝒪ₙ`, an integral domain.
* `ι : Polynomial R →+* B` — the inclusion `𝒪ₙ₋₁[w] ↪ 𝒪ₙ`, injective.
* `W : Submonoid (Polynomial R)` — the multiplicative set of **Weierstrass
  polynomials** (`1 ∈ W`, closed under products).

The Weierstrass Preparation Theorem provides:

* `hE` (existence): every nonzero `b ∈ 𝒪ₙ` is `ι g * u` for a Weierstrass
  polynomial `g` and a unit `u`;
* `hU` (uniqueness): the Weierstrass polynomial in such a representation is
  unique;
* `hD` (Gauss-type divisor closure): every divisor of a Weierstrass polynomial
  is associated to a Weierstrass polynomial (the irreducible factors of a
  Weierstrass polynomial are again Weierstrass).

Under these hypotheses we prove `UniqueFactorizationMonoid B`, i.e. `𝒪ₙ` is a
UFD.

The base case `𝒪₀ = ℂ` is a field, hence a UFD (`Mathlib`), so together with
this inductive step the full induction on `n` goes through.
-/

namespace WeierstrassUFD

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {B : Type*} [CommRing B] [IsDomain B]
variable (ι : Polynomial R →+* B) (hι : Function.Injective ι)
variable (W : Submonoid (Polynomial R))

/-
The heart of the argument: the image under `ι` of a *prime* Weierstrass
polynomial is prime in `B`.  This is where uniqueness in the WPT (`hU`) is used:
two Weierstrass polynomials with the same image (up to units) coincide.
-/
omit [UniqueFactorizationMonoid R] in
theorem prime_image_of_mem
    (hE : ∀ b : B, b ≠ 0 → ∃ g ∈ W, ∃ u : Bˣ, b = ι g * u)
    (hU : ∀ g ∈ W, ∀ g' ∈ W, ∀ u u' : Bˣ, ι g * (u : B) = ι g' * (u' : B) → g = g')
    {p : Polynomial R} (hpW : p ∈ W) (hp : Prime p) :
    Prime (ι p) := by
  refine' ⟨ _, _, _ ⟩;
  · intro h;
    contrapose! hU;
    refine' ⟨ p, hpW, p * p, W.mul_mem hpW hpW, 1, 1, _, _ ⟩ <;> simp +decide [ h ];
    by_cases h : p = 0 <;> simp_all +decide [ hp.ne_zero ];
    exact hp.ne_one;
  · intro h;
    specialize hU p hpW 1 ( Submonoid.one_mem _ ) 1 h.unit ; aesop;
  · intro a b hab
    by_cases ha : a = 0
    · simp [ha] at hab
      exact Or.inl (by
      simp +decide [ ha ])
    by_cases hb : b = 0
    · simp [hb] at hab
      exact Or.inr (by
      simp +decide [ hb ]);
    obtain ⟨gₐ, hgₐ, uₐ, ha⟩ := hE a ha
    obtain ⟨g_b, hg_b, u_b, hb⟩ := hE b hb
    obtain ⟨d, hd⟩ := hab
    by_cases hd0 : d = 0
    ·
      aesop
    obtain ⟨g_d, hg_d, u_d, hd⟩ := hE d hd0
    have h_eq : ι (gₐ * g_b) * (uₐ * u_b : Bˣ) = ι (p * g_d) * (u_d : Bˣ) := by
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ]
    have h_div : p ∣ gₐ * g_b := by
      specialize hU ( gₐ * g_b ) ( W.mul_mem hgₐ hg_b ) ( p * g_d ) ( W.mul_mem hpW hg_d ) ( uₐ * u_b ) u_d ; aesop ( simp_config := { singlePass := true } ) ;
    have h_div_ga_or_gb : p ∣ gₐ ∨ p ∣ g_b := by
      exact hp.dvd_or_dvd h_div
    generalize_proofs at *; (
    rcases h_div_ga_or_gb with ( h | h ) <;> [ left; right ] <;> obtain ⟨ q, hq ⟩ := h <;> simp +decide [ hq, ha, hb ] at *;)

/-
**Inductive step of "`𝒪ₙ` is a UFD".**  Assuming the Weierstrass
Preparation data (`hE`, `hU`, `hD`) relating the integral domain `B = 𝒪ₙ` to the
polynomial ring `Polynomial R = 𝒪ₙ₋₁[w]` over the UFD `R = 𝒪ₙ₋₁`, the ring `B`
is a unique factorization domain.
-/
theorem uniqueFactorizationMonoid_of_weierstrass
    (hE : ∀ b : B, b ≠ 0 → ∃ g ∈ W, ∃ u : Bˣ, b = ι g * u)
    (hU : ∀ g ∈ W, ∀ g' ∈ W, ∀ u u' : Bˣ, ι g * (u : B) = ι g' * (u' : B) → g = g')
    (hD : ∀ g ∈ W, ∀ d : Polynomial R, d ∣ g → ∃ d' ∈ W, Associated d' d) :
    UniqueFactorizationMonoid B := by
  apply_rules [ UniqueFactorizationMonoid.of_exists_prime_factors ];
  intro b hb;
  obtain ⟨g, hgW, u, hu⟩ := hE b hb;
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Multiset (Polynomial R), (∀ q ∈ f₀, Prime q) ∧ Associated f₀.prod g := by
    have := UniqueFactorizationMonoid.exists_prime_factors g ( by rintro rfl; simp_all +decide ) ; aesop;
  refine' ⟨ Multiset.map ( fun q => ι q ) f₀, _, _ ⟩ <;> simp_all +decide;
  · intro q hq
    obtain ⟨d', hd'W, hd'⟩ : ∃ d' ∈ W, Associated d' q := by
      exact hD g hgW q ( dvd_trans ( Multiset.dvd_prod hq ) ( hf₀.2.dvd ) )
    have h_prime_d' : Prime d' := by
      exact hd'.prime_iff.mpr ( hf₀.1 q hq )
    have h_prime_ι_d' : Prime (ι d') := by
      apply_rules [ WeierstrassUFD.prime_image_of_mem ]
    have h_assoc_ι_d' : Associated (ι d') (ι q) := hd'.map ι
    exact h_assoc_ι_d'.prime h_prime_ι_d'
  · rw [ ← map_multiset_prod ];
    exact hf₀.2.map ι

end WeierstrassUFD