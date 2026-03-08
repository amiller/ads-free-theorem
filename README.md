# Authenticated Data Structures, Generically

Agda formalization of soundness for authenticated data structures (generalized Merkle trees). The main theorem is **collision extraction**: if a verifier accepts two different results for the same query, we extract two distinct values with the same hash. This is the standard cryptographic security reduction, formalized as structural induction on a free monad of hash-checked lookups.

We compare two approaches to making this generic — parametric abstraction over references (following Atkey 2016) vs. polynomial functor codes — and show that only the latter produces efficient provers matching real Merkle tree protocols.

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

**Soundness:** if the verifier accepts two different answers for the same root digest, the two proof streams contain a pair of distinct values with the same hash.

## Two approaches

We present two ways to define generic authenticated data structures, each with different trade-offs.

### Approach 1: Parametric AuthKit (`GenericADS.agda`)

Define an `AuthKit` record with `Ref : Set → Set` and write data structures polymorphic over `Ref`:

```agda
data BST (F : Set → Set) : Set where
  leaf : ℕ → BST F
  node : F (BST F) → ℕ → F (BST F) → BST F
```

This is elegant — write once, instantiate with verifier or prover kit. But it has a fundamental efficiency problem: the prover's `unauth a = (a, [encode a])` serializes the **entire subtree** at each step, making authenticated lookups O(N) instead of O(log N). Atkey's parametricity approach has the same limitation — `unauth : {A} → Ref A → M A` is parametric in `A` and cannot do shallow encoding.

### Approach 2: Polynomial functor codes (`EfficientADS.agda`)

Define data structures as fixpoints of polynomial functor codes:

```agda
data Code : Set₁ where
  U : Code  ;  K : Set → Code  ;  I : Code
  _⊕_ _⊗_ : Code → Code → Code

bstC : Code
bstC = K ℕ ⊕ (I ⊗ K ℕ ⊗ I)    -- leaf n | node left key right
```

The prover uses **annotated trees** (`AFix c`) where each child carries `(subtree, digest)`. Operations are written once via a `Kit` record with `Ref : Code → Set` and `destruct`:

```agda
record Kit : Set₁ where
  field
    Ref      : Code → Set
    M        : Set → Set
    ret'     : {R : Set} → R → M R
    bind     : {R S : Set} → M R → (R → M S) → M S
    destruct : (c : Code) → Ref c → M (⟦ c ⟧ (Ref c))
```

The prover's `destruct` emits ONE encoded functor layer per step — O(1), matching real Merkle tree protocols. The verifier's `destruct` checks a hash and decodes. Operations like `lookup` are written once in a parameterized module and work with either kit.

### The trade-off

| | **Parametric (GenericADS)** | **Functor codes (EfficientADS)** |
|---|---|---|
| Data structure syntax | Natural Agda `data` | Codes: `K ℕ ⊕ (I ⊗ K ℕ ⊗ I)` |
| Write once? | Yes (polymorphic in Ref) | Yes (parameterized by Kit) |
| Prover efficiency | O(N) per query | O(log N) per query |
| Composition | Free (nest `F`) | Parameterized codes |

Both are write-once, but only the functor code approach produces efficient provers. The cost is uglier data structure definitions. A conjectured middle ground: a `deriving`-like mechanism (cf. GHC Generics, or Agda levitation) that extracts polynomial functor codes from ordinary data type definitions.

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
| `agda/EfficientADS.agda` | 313 | Polynomial functor codes, efficient O(log N) prover, collision extraction. Plain Agda, no sorry. |
| `agda/GenericADS.agda` | 286 | Parametric AuthKit, collision extraction, O(N) prover. Plain Agda, no sorry. |
| `agda/AtkeyCorrectness.agda` | 388 | Atkey's parametricity claim formalized via agda-bridges. No sorry. |
| `agda/TinyFreeThms.agda` | — | Warm-up: identity and Church bool free theorems |
| `agda/Noninterference.agda` | — | Noninterference from parametricity |

## Development

`EfficientADS.agda` and `GenericADS.agda` are **plain Agda** — any standard Agda installation can typecheck them:

```bash
agda agda/EfficientADS.agda
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
