-- Collision extraction for authenticated data structures (Layer 2).
--
-- A computation is a tree of hash-checked lookups (free monad).
-- If two proof streams both pass verification for the same computation
-- but produce different results, we extract a hash collision.
--
-- Layer 1 (AuthFreeThm.agda): parametricity → honest computation is pure
-- Layer 2 (this file): wrong result accepted → collision in hash
--
-- Self-contained, no library dependencies.

module CollisionExtraction where

-- ================================================================
-- Prelude

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

data ⊥ : Set where
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field fst : A ; snd : B fst
open Σ public

_×_ : Set → Set → Set
A × B = Σ A λ _ → B
infixr 4 _,_
infixr 2 _×_


-- ================================================================
-- Parameters

postulate
  Val Digest : Set
  hash   : Val → Digest
  _≟V_   : (x y : Val)    → (x ≡ y) ⊎ ((x ≡ y) → ⊥)
  _≟D_   : (x y : Digest) → (x ≡ y) ⊎ ((x ≡ y) → ⊥)


-- ================================================================
-- Computation tree (free monad of hash-checked lookups)
--
-- ret r:      return r
-- step d k:   "give me v with hash v = d, then continue with k v"

data Comp (R : Set) : Set where
  ret  : R → Comp R
  step : Digest → (Val → Comp R) → Comp R


-- ================================================================
-- Verifier: run a computation against a proof stream

data Outcome (R : Set) : Set where
  ok   : R → List Val → Outcome R
  fail : Outcome R

run : {R : Set} → Comp R → List Val → Outcome R
run (ret r)    s       = ok r s
run (step d k) []      = fail
run (step d k) (v ∷ s) with d ≟D hash v
... | inl _ = run (k v) s
... | inr _ = fail


-- ================================================================
-- Collision

Collision : Set
Collision = Σ Val λ x → Σ Val λ y → ((x ≡ y) → ⊥) × (hash x ≡ hash y)


-- ================================================================
-- Main theorem
--
-- If two proof streams both pass verification for the same computation
-- but produce different results, we extract a hash collision.
--
-- Proof: induction on the computation tree.
--   ret:  both runs return the same value — contradiction.
--   step d k:  both streams provide v₁, v₂ with hash matching d.
--     v₁ ≠ v₂ → collision (hash v₁ = d = hash v₂ but v₁ ≠ v₂).
--     v₁ = v₂ → recurse on k v₁ with remaining streams.

fail≢ok : {R : Set} {r : R} {s : List Val} → _≡_ {Outcome R} fail (ok r s) → ⊥
fail≢ok ()

ok-inj : {R : Set} {r₁ r₂ : R} {s₁ s₂ : List Val} →
  _≡_ {Outcome R} (ok r₁ s₁) (ok r₂ s₂) → r₁ ≡ r₂
ok-inj refl = refl

extract : {R : Set} (c : Comp R) (s₁ s₂ : List Val)
  {r₁ r₂ : R} {s₁' s₂' : List Val}
  → run c s₁ ≡ ok r₁ s₁'
  → run c s₂ ≡ ok r₂ s₂'
  → (r₁ ≡ r₂ → ⊥)
  → Collision
extract (ret r) s₁ s₂ p₁ p₂ neq =
  ⊥-elim (neq (trans (sym (ok-inj p₁)) (ok-inj p₂)))
extract (step d k) [] s₂ p₁ p₂ neq =
  ⊥-elim (fail≢ok p₁)
extract (step d k) (v₁ ∷ s₁) [] p₁ p₂ neq =
  ⊥-elim (fail≢ok p₂)
extract (step d k) (v₁ ∷ s₁) (v₂ ∷ s₂) p₁ p₂ neq with d ≟D hash v₁
... | inr _ = ⊥-elim (fail≢ok p₁)
... | inl eq₁ with d ≟D hash v₂
...   | inr _ = ⊥-elim (fail≢ok p₂)
...   | inl eq₂ with v₁ ≟V v₂
...     | inr v≠ = v₁ , v₂ , v≠ , trans (sym eq₁) eq₂
...     | inl refl = extract (k v₁) s₁ s₂ p₁ p₂ neq
