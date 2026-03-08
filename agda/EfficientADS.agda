-- Efficient Authenticated Data Structures via Polynomial Functor Codes
--
-- Contrast with GenericADS.agda which uses a parametric AuthKit (Ref : Set → Set).
-- That approach has an O(N) prover bug: unauth encodes entire subtrees.
--
-- Here, data structures are defined as fixpoints of polynomial functor codes.
-- The prover uses annotated trees (each child carries subtree + digest) and
-- emits ONE functor layer per destruct — O(1) per step, O(log N) for a search.
--
-- The collision extraction theorem is identical: it depends only on Comp,
-- not on how the data structure or prover is organized.
--
-- Self-contained, plain Agda, no library dependencies.

module EfficientADS where

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

record ⊤ : Set where
  constructor tt

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data Bool : Set where
  false true : Bool

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A


-- ================================================================
-- Parameters

postulate
  Val Digest : Set
  hash   : Val → Digest
  _≟V_   : (x y : Val)    → (x ≡ y) ⊎ ((x ≡ y) → ⊥)
  _≟D_   : (x y : Digest) → (x ≡ y) ⊎ ((x ≡ y) → ⊥)
  encode : {A : Set} → A → Val
  decode : {A : Set} → Val → A


-- ================================================================
-- Computation tree (free monad of hash-checked lookups)

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
-- Collision extraction

Collision : Set
Collision = Σ Val λ x → Σ Val λ y → ((x ≡ y) → ⊥) × (hash x ≡ hash y)

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
-- Polynomial functor codes

data Code : Set₁ where
  U     : Code
  K     : Set → Code
  I     : Code
  _⊕_ _⊗_ : Code → Code → Code
infixr 5 _⊕_
infixr 6 _⊗_

⟦_⟧ : Code → Set → Set
⟦ U ⟧     X = ⊤
⟦ K A ⟧   X = A
⟦ I ⟧     X = X
⟦ c ⊕ d ⟧ X = ⟦ c ⟧ X ⊎ ⟦ d ⟧ X
⟦ c ⊗ d ⟧ X = ⟦ c ⟧ X × ⟦ d ⟧ X

fmap : (c : Code) {X Y : Set} → (X → Y) → ⟦ c ⟧ X → ⟦ c ⟧ Y
fmap U       f tt      = tt
fmap (K A)   f a       = a
fmap I       f x       = f x
fmap (c ⊕ d) f (inl x) = inl (fmap c f x)
fmap (c ⊕ d) f (inr y) = inr (fmap d f y)
fmap (c ⊗ d) f (x , y) = fmap c f x , fmap d f y


-- ================================================================
-- Fixpoint and annotated fixpoint

{-# NO_POSITIVITY_CHECK #-}
data Fix (c : Code) : Set where
  In : ⟦ c ⟧ (Fix c) → Fix c

-- Each recursive position carries (subtree, digest)
-- Mirrors Merkle.hs: Annot f = f ∘ (I × K D)
{-# NO_POSITIVITY_CHECK #-}
data AFix (c : Code) : Set where
  AIn : ⟦ c ⟧ (AFix c × Digest) → AFix c

-- Hash one functor layer (digests at recursive positions)
hhash : (c : Code) → ⟦ c ⟧ Digest → Digest
hhash c layer = hash (encode layer)

-- Root digest of an annotated tree
adigest : (c : Code) → AFix c → Digest
adigest c (AIn layer) = hhash c (fmap c snd layer)

-- Bottom-up annotation: compute digest at each node
{-# TERMINATING #-}
annotate : (c : Code) → Fix c → AFix c
annotate c (In layer) = AIn (fmap c (λ t → let at = annotate c t in at , adigest c at) layer)


-- ================================================================
-- Writer monad (prover output)

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

Writer : Set → Set
Writer R = R × List Val

bindW : {R S : Set} → Writer R → (R → Writer S) → Writer S
bindW (r , s₁) f = f r .fst , s₁ ++ f r .snd


-- ================================================================
-- Verifier destruct and prover destruct

v-destruct : (c : Code) → Digest → Comp (⟦ c ⟧ Digest)
v-destruct c d = step d (λ v → ret (decode v))

p-destruct : (c : Code) → AFix c → Writer (⟦ c ⟧ (AFix c))
p-destruct c (AIn layer) =
  fmap c fst layer , encode (fmap c snd layer) ∷ []


-- ================================================================
-- BST example

bstC : Code
bstC = K ℕ ⊕ (I ⊗ K ℕ ⊗ I)

_<?_ : ℕ → ℕ → Bool
zero  <? zero  = false
zero  <? suc _ = true
suc _ <? zero  = false
suc m <? suc n = m <? n

-- Verifier lookup: produces Comp ℕ
{-# TERMINATING #-}
v-lookup : ℕ → Digest → Comp ℕ
v-lookup q d = bindC (v-destruct bstC d) go
  where
  go : ⟦ bstC ⟧ Digest → Comp ℕ
  go (inl n)               = ret n
  go (inr (l , k , r)) with q <? k
  ... | true  = v-lookup q l
  ... | false = v-lookup q r

-- Prover lookup: produces Writer ℕ, O(log N) proof stream
{-# TERMINATING #-}
p-lookup : ℕ → AFix bstC → Writer ℕ
p-lookup q at = bindW (p-destruct bstC at) go
  where
  go : ⟦ bstC ⟧ (AFix bstC) → Writer ℕ
  go (inl n)               = n , []
  go (inr (l , k , r)) with q <? k
  ... | true  = p-lookup q l
  ... | false = p-lookup q r

-- Soundness: two proof streams, same digest, different results → collision
bst-soundness : (q : ℕ) (root : Digest)
  (s₁ s₂ : List Val) {r₁ r₂ : ℕ} {s₁' s₂' : List Val}
  → run (v-lookup q root) s₁ ≡ ok r₁ s₁'
  → run (v-lookup q root) s₂ ≡ ok r₂ s₂'
  → (r₁ ≡ r₂ → ⊥)
  → Collision
bst-soundness q root = extract (v-lookup q root)


-- ================================================================
-- Composed example: list of BSTs
--
-- AList is parameterized by the BST reference type:
--   Verifier: alistC Digest     (BST refs are digests)
--   Prover:   alistC (AFix bstC) (BST refs are annotated trees)

alistC : Set → Code
alistC R = U ⊕ (K R ⊗ I)

-- Verifier: index into list, then lookup in BST
{-# TERMINATING #-}
v-index : ℕ → Digest → Comp (Maybe Digest)
v-index i d = bindC (v-destruct (alistC Digest) d) (go i)
  where
  go : ℕ → ⟦ alistC Digest ⟧ Digest → Comp (Maybe Digest)
  go i       (inl tt)          = ret nothing
  go zero    (inr (bst , _))   = ret (just bst)
  go (suc n) (inr (_   , tl))  = v-index n tl

v-lookupAt : ℕ → ℕ → Digest → Comp (Maybe ℕ)
v-lookupAt i q root = bindC (v-index i root) go
  where
  go : Maybe Digest → Comp (Maybe ℕ)
  go nothing    = ret nothing
  go (just bst) = bindC (v-lookup q bst) (λ n → ret (just n))

-- Prover: index into annotated list, then lookup in annotated BST
{-# TERMINATING #-}
p-index : ℕ → AFix (alistC (AFix bstC)) → Writer (Maybe (AFix bstC))
p-index i at = bindW (p-destruct (alistC (AFix bstC)) at) (go i)
  where
  go : ℕ → ⟦ alistC (AFix bstC) ⟧ (AFix (alistC (AFix bstC))) → Writer (Maybe (AFix bstC))
  go i       (inl tt)          = nothing , []
  go zero    (inr (bst , _))   = just bst , []
  go (suc n) (inr (_   , tl))  = p-index n tl

p-lookupAt : ℕ → ℕ → AFix (alistC (AFix bstC)) → Writer (Maybe ℕ)
p-lookupAt i q root = bindW (p-index i root) go
  where
  go : Maybe (AFix bstC) → Writer (Maybe ℕ)
  go nothing    = nothing , []
  go (just bst) = bindW (p-lookup q bst) (λ n → just n , [])

-- Soundness for composed lookups
alist-soundness : (i q : ℕ) (root : Digest)
  (s₁ s₂ : List Val) {r₁ r₂ : Maybe ℕ} {s₁' s₂' : List Val}
  → run (v-lookupAt i q root) s₁ ≡ ok r₁ s₁'
  → run (v-lookupAt i q root) s₂ ≡ ok r₂ s₂'
  → (r₁ ≡ r₂ → ⊥)
  → Collision
alist-soundness i q root = extract (v-lookupAt i q root)
