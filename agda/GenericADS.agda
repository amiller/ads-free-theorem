-- Generic Authenticated Data Structures: Soundness via Collision Extraction
--
-- We define a generic AuthKit interface for authenticated data structures:
--   auth   : A → Ref A      (wrap a value — hash it or keep it)
--   unauth : Ref A → M A    (unwrap — check hash or return directly)
--
-- Data structures are written once, polymorphic over Ref : Set → Set.
-- Instantiating with VerifierKit produces a computation tree (Comp R),
-- a free monad of hash-checked lookups. We prove:
--
--   If two proof streams both pass verification but produce different
--   results, we extract a collision in the hash function.
--
-- Examples: authenticated BST, and a composed list-of-BSTs showing
-- that auth composes freely across data structures.
--
-- Self-contained, plain Agda, no library dependencies.

module GenericADS where

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

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data Bool : Set where
  false true : Bool


-- ================================================================
-- Parameters

postulate
  Val Digest : Set
  hash   : Val → Digest
  _≟V_   : (x y : Val)    → (x ≡ y) ⊎ ((x ≡ y) → ⊥)
  _≟D_   : (x y : Digest) → (x ≡ y) ⊎ ((x ≡ y) → ⊥)
  -- Serialization: auth can only apply to types with encode/decode.
  -- In practice this means algebraic data, not function types.
  encode : {A : Set} → A → Val
  decode : {A : Set} → Val → A


-- ================================================================
-- Computation tree (free monad of hash-checked lookups)
--
-- ret r:      return r
-- step d k:   "give me v with hash v = d, then continue with k v"

data Comp (R : Set) : Set where
  ret  : R → Comp R
  step : Digest → (Val → Comp R) → Comp R

bindC : {R S : Set} → Comp R → (R → Comp S) → Comp S
bindC (ret r)    f = f r
bindC (step d k) f = step d (λ v → bindC (k v) f)


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
-- Collision extraction
--
-- If two proof streams both pass verification for the same computation
-- but produce different results, we extract a hash collision.

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


-- ================================================================
-- Auth Kit interface
--
-- Ref : Set → Set   — authenticated reference (Digest or identity)
-- auth : A → Ref A  — wrap a value (hash it or keep it)
-- unauth : Ref A → M A — unwrap (verify hash or return directly)
--
-- auth only makes sense for serializable (algebraic) types.
-- Function types cannot be authenticated.

record AuthKit : Set₁ where
  field
    Ref    : Set → Set
    M      : Set → Set
    pure   : {R : Set} → R → M R
    _>>=_  : {R S : Set} → M R → (R → M S) → M S
    auth   : {A : Set} → A → Ref A
    unauth : {A : Set} → Ref A → M A


-- ================================================================
-- Verifier Kit: Ref A = Digest, M = Comp

VerifierKit : AuthKit
VerifierKit = record
  { Ref = λ _ → Digest ; M = Comp
  ; pure = ret ; _>>=_ = bindC
  ; auth = λ a → hash (encode a)
  ; unauth = λ d → step d (λ v → ret (decode v)) }


-- ================================================================
-- Prover Kit: Ref A = A, M = Writer (result × proof stream)

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

Writer : Set → Set
Writer R = R × List Val

ProverKit : AuthKit
ProverKit = record
  { Ref = λ A → A ; M = Writer
  ; pure = λ r → r , []
  ; _>>=_ = λ { (r , s₁) f → f r .fst , s₁ ++ f r .snd }
  ; auth = λ a → a
  ; unauth = λ a → a , encode a ∷ [] }


-- ================================================================
-- Example: authenticated BST
--
-- Written once, polymorphic over the kit. Children are Ref (BST Ref).
-- Verifier: children are Digests, lookup produces Comp ℕ.
-- Prover: children are subtrees, lookup produces (ℕ , proof stream).

{-# NO_POSITIVITY_CHECK #-}
data BST (F : Set → Set) : Set where
  leaf : ℕ → BST F
  node : F (BST F) → ℕ → F (BST F) → BST F

_<?_ : ℕ → ℕ → Bool
zero  <? zero  = false
zero  <? suc _ = true
suc _ <? zero  = false
suc m <? suc n = m <? n

module BSTOps (k : AuthKit) where
  open AuthKit k

  {-# TERMINATING #-}
  lookup : ℕ → Ref (BST Ref) → M ℕ
  lookup q ref = unauth ref >>= go
    where
    go : BST Ref → M ℕ
    go (leaf n) = pure n
    go (node l key r) with q <? key
    ... | true  = lookup q l
    ... | false = lookup q r


-- ================================================================
-- Soundness: BST lookup instantiated with VerifierKit gives Comp ℕ.
-- Two proof streams, same tree, different results → collision.

bst-soundness : (q : ℕ) (root : Digest)
  (s₁ s₂ : List Val) {r₁ r₂ : ℕ} {s₁' s₂' : List Val}
  → run (BSTOps.lookup VerifierKit q root) s₁ ≡ ok r₁ s₁'
  → run (BSTOps.lookup VerifierKit q root) s₂ ≡ ok r₂ s₂'
  → (r₁ ≡ r₂ → ⊥)
  → Collision
bst-soundness q root = extract (BSTOps.lookup VerifierKit q root)


-- ================================================================
-- Composed example: authenticated list of authenticated BSTs
--
-- Demonstrates that auth composes freely across data structures.
-- The proof stream is flat (List Val) — each unauth adds one step,
-- regardless of what type is being unwrapped.

{-# NO_POSITIVITY_CHECK #-}
data AList (F : Set → Set) : Set where
  nil  : AList F
  cons : F (BST F) → F (AList F) → AList F

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

module AListOps (k : AuthKit) where
  open AuthKit k
  open BSTOps k using (lookup)

  {-# TERMINATING #-}
  index : ℕ → Ref (AList Ref) → M (Maybe (Ref (BST Ref)))
  index i ref = unauth ref >>= go i
    where
    go : ℕ → AList Ref → M (Maybe (Ref (BST Ref)))
    go i nil = pure nothing
    go zero    (cons bst rest) = pure (just bst)
    go (suc n) (cons bst rest) = index n rest

  -- Look up query q in the i-th BST
  lookupAt : ℕ → ℕ → Ref (AList Ref) → M (Maybe ℕ)
  lookupAt i q ref = index i ref >>= go
    where
    go : Maybe (Ref (BST Ref)) → M (Maybe ℕ)
    go nothing    = pure nothing
    go (just bst) = lookup q bst >>= λ n → pure (just n)

-- Soundness for composed lookups
alist-soundness : (i q : ℕ) (root : Digest)
  (s₁ s₂ : List Val) {r₁ r₂ : Maybe ℕ} {s₁' s₂' : List Val}
  → run (AListOps.lookupAt VerifierKit i q root) s₁ ≡ ok r₁ s₁'
  → run (AListOps.lookupAt VerifierKit i q root) s₂ ≡ ok r₂ s₂'
  → (r₁ ≡ r₂ → ⊥)
  → Collision
alist-soundness i q root = extract (AListOps.lookupAt VerifierKit i q root)
