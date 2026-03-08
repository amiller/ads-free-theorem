-- Atkey-style Authenticated Data Structures with Efficient Prover
--
-- Combines the best of GenericADS and EfficientADS:
--   - Natural data types (parametric Ref : Set → Set), like GenericADS
--   - O(log N) prover, like EfficientADS
--
-- The key idea (from Gregersen et al. 2025, following Atkey 2016):
--   auth/unauth take an Enc record for type-specific serialization,
--   and Kit provides ref-dig : Ref A → Digest so Enc instances can
--   extract digests from children without recursing into subtrees.
--
-- ProverKit: Ref A = A × Digest, auth stores (value, digest),
--   unauth emits ser enc x which is O(1) when ser uses ref-dig.
--
-- Self-contained, plain Agda, no library dependencies.

module AtkeyADS where

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
-- Type-specific serialization

record Enc (A : Set) : Set where
  field ser : A → Val ; des : Val → A


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
-- Kit: Enc-parameterized auth/unauth + ref-dig

record Kit : Set₁ where
  field
    Ref     : Set → Set
    M       : Set → Set
    ret'    : {R : Set} → R → M R
    bind    : {R S : Set} → M R → (R → M S) → M S
    auth    : {A : Set} → Enc A → A → Ref A
    unauth  : {A : Set} → Enc A → Ref A → M A
    ref-dig : {A : Set} → Ref A → Digest

VerifierKit : Kit
VerifierKit = record
  { Ref = λ _ → Digest ; M = Comp
  ; ret' = ret ; bind = bindC
  ; auth = λ enc x → hash (Enc.ser enc x)
  ; unauth = λ enc d → step d (λ v → ret (Enc.des enc v))
  ; ref-dig = λ d → d }

ProverKit : Kit
ProverKit = record
  { Ref = λ X → X × Digest ; M = Writer
  ; ret' = λ r → r , [] ; bind = bindW
  ; auth = λ enc x → x , hash (Enc.ser enc x)
  ; unauth = λ { enc (x , d) → x , Enc.ser enc x ∷ [] }
  ; ref-dig = snd }


-- ================================================================
-- BST: natural data type, parametric over Ref

{-# NO_POSITIVITY_CHECK #-}
data BST (F : Set → Set) : Set where
  leaf : ℕ → BST F
  node : F (BST F) → ℕ → F (BST F) → BST F

_<?_ : ℕ → ℕ → Bool
zero  <? zero  = false
zero  <? suc _ = true
suc _ <? zero  = false
suc m <? suc n = m <? n

module BSTOps (k : Kit) where
  open Kit k

  encBST : Enc (BST Ref)
  encBST = record { ser = go ; des = decode }
    where
    go : BST Ref → Val
    go (leaf n)     = encode {ℕ ⊎ (Digest × ℕ × Digest)} (inl n)
    go (node l k r) = encode {ℕ ⊎ (Digest × ℕ × Digest)} (inr (ref-dig l , k , ref-dig r))

  {-# TERMINATING #-}
  lookup : ℕ → Ref (BST Ref) → M ℕ
  lookup q ref = bind (unauth encBST ref) go
    where
    go : BST Ref → M ℕ
    go (leaf n) = ret' n
    go (node l key r) with q <? key
    ... | true  = lookup q l
    ... | false = lookup q r


-- ================================================================
-- Soundness: BST

bst-soundness : (q : ℕ) (root : Digest)
  (s₁ s₂ : List Val) {r₁ r₂ : ℕ} {s₁' s₂' : List Val}
  → run (BSTOps.lookup VerifierKit q root) s₁ ≡ ok r₁ s₁'
  → run (BSTOps.lookup VerifierKit q root) s₂ ≡ ok r₂ s₂'
  → (r₁ ≡ r₂ → ⊥)
  → Collision
bst-soundness q root = extract (BSTOps.lookup VerifierKit q root)


-- ================================================================
-- Composed example: authenticated list of BSTs

{-# NO_POSITIVITY_CHECK #-}
data AList (F : Set → Set) : Set where
  nil  : AList F
  cons : F (BST F) → F (AList F) → AList F

module AListOps (k : Kit) where
  open Kit k
  open BSTOps k using (lookup ; encBST)

  encAList : Enc (AList Ref)
  encAList = record { ser = go ; des = decode }
    where
    go : AList Ref → Val
    go nil          = encode {⊤ ⊎ (Digest × Digest)} (inl tt)
    go (cons b r)   = encode {⊤ ⊎ (Digest × Digest)} (inr (ref-dig b , ref-dig r))

  {-# TERMINATING #-}
  index : ℕ → Ref (AList Ref) → M (Maybe (Ref (BST Ref)))
  index i ref = bind (unauth encAList ref) (go i)
    where
    go : ℕ → AList Ref → M (Maybe (Ref (BST Ref)))
    go i nil = ret' nothing
    go zero    (cons bst rest) = ret' (just bst)
    go (suc n) (cons bst rest) = index n rest

  lookupAt : ℕ → ℕ → Ref (AList Ref) → M (Maybe ℕ)
  lookupAt i q ref = bind (index i ref) go
    where
    go : Maybe (Ref (BST Ref)) → M (Maybe ℕ)
    go nothing    = ret' nothing
    go (just bst) = bind (lookup q bst) (λ n → ret' (just n))


-- ================================================================
-- Soundness: AList

alist-soundness : (i q : ℕ) (root : Digest)
  (s₁ s₂ : List Val) {r₁ r₂ : Maybe ℕ} {s₁' s₂' : List Val}
  → run (AListOps.lookupAt VerifierKit i q root) s₁ ≡ ok r₁ s₁'
  → run (AListOps.lookupAt VerifierKit i q root) s₂ ≡ ok r₂ s₂'
  → (r₁ ≡ r₂ → ⊥)
  → Collision
alist-soundness i q root = extract (AListOps.lookupAt VerifierKit i q root)
