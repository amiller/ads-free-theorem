# Generic Authenticated Data Structures

Soundness proof for authenticated data structures in Agda: if an adversary fools the verifier, we extract a hash collision. The formalization provides a generic `AuthKit` interface — write a data structure once, get prover and verifier for free — and proves soundness for any program built against it.

## The Merkle BST protocol

A binary search tree where each node is identified by its hash digest:

```
     h(root)
      /   \
   h(L)   h(R)       ← digests
   / \     / \
  ...     ...         ← full tree (prover has this)
```

**Prover** holds the full tree. To answer a lookup query, it traverses the tree and records each visited node in a *proof stream*.

**Verifier** holds only the root digest. It replays the traversal: for each step, it pops a node from the proof stream, checks `hash(node) == expected digest`, then descends into the appropriate child digest.

**Soundness claim:** if the verifier accepts a wrong answer, then the proof stream contains two different values with the same hash — a collision.

## The generic interface

Rather than hardcoding BSTs, we define an `AuthKit` that any data structure can use:

```agda
record AuthKit : Set₁ where
  field
    Ref    : Set → Set                                  -- authenticated reference
    M      : Set → Set                                  -- computation monad
    pure   : {R : Set} → R → M R
    _>>=_  : {R S : Set} → M R → (R → M S) → M S
    auth   : {A : Set} → A → Ref A                     -- wrap (hash or keep)
    unauth : {A : Set} → Ref A → M A                   -- unwrap (verify or return)
```

Two concrete kits:

| | **Verifier** | **Prover** |
|---|---|---|
| `Ref A` | `Digest` | `A` |
| `M R` | `Comp R` (free monad) | `R × List Val` (writer) |
| `auth a` | `hash (encode a)` | `a` |
| `unauth ref` | `step ref (decode ∘ ret)` | `(a, [encode a])` |

A data structure is defined once, polymorphic over `Ref`:

```agda
data BST (F : Set → Set) : Set where
  leaf : ℕ → BST F
  node : F (BST F) → ℕ → F (BST F) → BST F
```

Operations use `auth`/`unauth` from any kit:

```agda
lookup : (k : AuthKit) → ℕ → Ref (BST Ref) → M ℕ
lookup k q ref = unauth ref >>= λ where
  (leaf n)       → pure n
  (node l key r) → if q < key then lookup k q l else lookup k q r
```

Instantiate with `VerifierKit` → get a `Comp ℕ` (computation tree of hash-checked lookups). This composes freely: a list of BSTs, a tree of lists, etc. The proof stream is flat `List Val` regardless of the types involved.

## The soundness theorem

A computation tree is a free monad of hash-checked lookups:

```agda
data Comp (R : Set) : Set where
  ret  : R → Comp R
  step : Digest → (Val → Comp R) → Comp R
```

The verifier runs a computation against a proof stream, checking each hash:

```agda
run : Comp R → List Val → Outcome R
run (ret r)    s       = ok r s
run (step d k) []      = fail
run (step d k) (v ∷ s) = if hash v == d then run (k v) s else fail
```

**Collision extraction:** if two proof streams both pass verification for the same computation but produce different results, we extract a hash collision.

```agda
extract : (c : Comp R) (s₁ s₂ : List Val)
  → run c s₁ ≡ ok r₁  → run c s₂ ≡ ok r₂  → r₁ ≠ r₂  → Collision
```

Proof: induction on the computation tree. At each `step d k`, both streams provide values `v₁, v₂` with `hash v₁ = d = hash v₂`. Either `v₁ ≠ v₂` (collision found) or `v₁ = v₂` (recurse). The collision lives at the first divergence point.

## Comparison with Atkey (2016)

Atkey [claimed](https://bentnib.org/posts/2016-04-12-authenticated-data-structures-as-a-library.html) that parametricity over the auth interface gives security "for free." We formalize this claim (in `AtkeyCorrectness.agda` using agda-bridges) but find it proves something weaker than soundness:

- **Atkey's result** requires a "round-trip law": `unauth (auth x) ≡ ret x`. The verifier does not satisfy this — its `unauth` reads from an external proof stream, not from `auth`'s output. The law holds for honest kits (prover, identity) but not for the adversarial case.

- **Our result** (collision extraction) requires no laws at all. It works directly on the computation tree produced by the verifier kit. The security reduction is: wrong answer accepted → collision in hash. This is the standard cryptographic argument, formalized as 30 lines of induction.

## Files

| File | Lines | Description |
|------|-------|-------------|
| `agda/GenericADS.agda` | 278 | Main formalization: kit interface, kits, collision extraction, BST, composed list-of-BSTs example. Self-contained, plain Agda, no sorry. |
| `agda/AtkeyCorrectness.agda` | 388 | Atkey's parametricity claim formalized via agda-bridges. Proves honest computations are pure. Requires cubical Agda + bridges. No sorry. |
| `agda/TinyFreeThms.agda` | — | Warm-up: identity and Church bool free theorems |
| `agda/Noninterference.agda` | — | Noninterference from parametricity |

## Development

`GenericADS.agda` is **plain Agda** — any standard Agda installation can typecheck it:

```bash
agda agda/GenericADS.agda
```

`AtkeyCorrectness.agda` requires a patched Agda with bridge types. See the `agda-check` script and setup notes below.

<details>
<summary>agda-bridges setup (for AtkeyCorrectness.agda only)</summary>

Requires Docker and ~4GB disk.

```bash
# 1. Get compiler source
git clone https://music-impl.pages.gitlabpages.inria.fr/agda-music-graded/agda-bridges.git ~/agda-bridges-src
cd ~/agda-bridges-src && git checkout bridges-with-2.6.4

# 2. Build (see agda-check script for Docker invocation)
# 3. Get cubical + bridgy-lib libraries
# 4. Typecheck
./agda-check agda/AtkeyCorrectness.agda
```

</details>

## References

- Miller, Hicks, Katz, Shi — [Authenticated Data Structures, Generically, with Bilinear Accumulators](https://amiller.github.io/lambda-auth/) (POPL 2014)
- Atkey — [Authenticated Data Structures, Generically](https://bentnib.org/posts/2016-04-12-authenticated-data-structures-as-a-library.html) (2016 blog)
- Miller — [generic-ads](https://github.com/amiller/generic-ads) (2013 Haskell implementation)
- Miller — [redblackmerkle](https://github.com/amiller/redblackmerkle) (2012 Python/Haskell/C++ implementation)
