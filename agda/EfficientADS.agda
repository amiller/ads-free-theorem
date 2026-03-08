-- Efficient Authenticated Data Structures via Polynomial Functor Codes
--
-- Contrast with GenericADS.agda which uses a parametric AuthKit (Ref : Set → Set).
-- That approach has an O(N) prover bug: unauth encodes entire subtrees.
--
-- Here, data structures are defined as fixpoints of polynomial functor codes.
-- The prover uses annotated trees (each child carries subtree + digest) and
-- emits ONE functor layer per unauth — O(1) per step, O(log N) for a search.
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
-- Auth Kit: write operations once, instantiate for prover or verifier
--
-- Ref : Code → Set maps each data structure code to its reference type.
--   Verifier: Ref _ = Digest
--   Prover:   Ref c = AFix c
--
-- unauth peels one layer of a reference, returning the functor applied
-- to child references. This is where efficiency lives: the prover emits
-- one encoded layer per unauth, not the entire subtree.

record Kit : Set₁ where
  field
    Ref      : Code → Set
    M        : Set → Set
    ret'     : {R : Set} → R → M R
    bind     : {R S : Set} → M R → (R → M S) → M S
    unauth : (c : Code) → Ref c → M (⟦ c ⟧ (Ref c))

VerifierKit : Kit
VerifierKit = record
  { Ref = λ _ → Digest ; M = Comp
  ; ret' = ret ; bind = bindC
  ; unauth = λ c d → step d (λ v → ret (decode v)) }

ProverKit : Kit
ProverKit = record
  { Ref = AFix ; M = Writer
  ; ret' = λ r → r , [] ; bind = bindW
  ; unauth = λ { c (AIn layer) → fmap c fst layer , encode (fmap c snd layer) ∷ [] } }


-- ================================================================
-- BST example — written once, works for both kits

bstC : Code
bstC = K ℕ ⊕ (I ⊗ K ℕ ⊗ I)

_<?_ : ℕ → ℕ → Bool
zero  <? zero  = false
zero  <? suc _ = true
suc _ <? zero  = false
suc m <? suc n = m <? n

module BSTOps (k : Kit) where
  open Kit k

  {-# TERMINATING #-}
  lookup : ℕ → Ref bstC → M ℕ
  lookup q ref = bind (unauth bstC ref) go
    where
    go : ⟦ bstC ⟧ (Ref bstC) → M ℕ
    go (inl n)           = ret' n
    go (inr (l , n , r)) with q <? n
    ... | true  = lookup q l
    ... | false = lookup q r

bst-soundness : (q : ℕ) (root : Digest)
  (s₁ s₂ : List Val) {r₁ r₂ : ℕ} {s₁' s₂' : List Val}
  → run (BSTOps.lookup VerifierKit q root) s₁ ≡ ok r₁ s₁'
  → run (BSTOps.lookup VerifierKit q root) s₂ ≡ ok r₂ s₂'
  → (r₁ ≡ r₂ → ⊥)
  → Collision
bst-soundness q root = extract (BSTOps.lookup VerifierKit q root)


-- ================================================================
-- Composed example: list of BSTs — also written once

alistC : Set → Code
alistC R = U ⊕ (K R ⊗ I)

module AListOps (k : Kit) where
  open Kit k
  open BSTOps k using (lookup)

  {-# TERMINATING #-}
  index : ℕ → Ref (alistC (Ref bstC)) → M (Maybe (Ref bstC))
  index i ref = bind (unauth (alistC (Ref bstC)) ref) (go i)
    where
    go : ℕ → ⟦ alistC (Ref bstC) ⟧ (Ref (alistC (Ref bstC))) → M (Maybe (Ref bstC))
    go i       (inl tt)          = ret' nothing
    go zero    (inr (bst , _))   = ret' (just bst)
    go (suc n) (inr (_   , tl))  = index n tl

  lookupAt : ℕ → ℕ → Ref (alistC (Ref bstC)) → M (Maybe ℕ)
  lookupAt i q ref = bind (index i ref) go
    where
    go : Maybe (Ref bstC) → M (Maybe ℕ)
    go nothing    = ret' nothing
    go (just bst) = bind (lookup q bst) (λ n → ret' (just n))

alist-soundness : (i q : ℕ) (root : Digest)
  (s₁ s₂ : List Val) {r₁ r₂ : Maybe ℕ} {s₁' s₂' : List Val}
  → run (AListOps.lookupAt VerifierKit i q root) s₁ ≡ ok r₁ s₁'
  → run (AListOps.lookupAt VerifierKit i q root) s₂ ≡ ok r₂ s₂'
  → (r₁ ≡ r₂ → ⊥)
  → Collision
alist-soundness i q root = extract (AListOps.lookupAt VerifierKit i q root)
