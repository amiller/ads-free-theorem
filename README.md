# Authenticated Data Structures, Generically

Agda formalization of soundness for authenticated data structures (Merkle trees). The main theorem is **collision extraction**: if a verifier accepts two different results for the same query, we extract a hash collision. Plain Agda, no sorry, 284 lines.

## The protocol

A binary search tree where each node is identified by its hash digest:

```
     h(root)
      /   \
   h(L)   h(R)       ← digests
   / \     / \
  ...     ...         ← full tree (prover has this)
```

**Prover** holds the full tree. To answer a lookup, it traverses and records each visited node in a *proof stream* — one shallow encoding per node, O(log N) total.

**Verifier** holds only the root digest. It pops nodes from the proof stream, checks hashes, and descends into child digests.

**Soundness:** two accepted answers for the same root → hash collision.

## Design: Atkey-style Kit with `Enc`

Data structures are natural Agda types, parametric over `Ref : Set → Set`:

```agda
data BST (F : Set → Set) : Set where
  leaf : ℕ → BST F
  node : F (BST F) → ℕ → F (BST F) → BST F
```

The `Kit` record provides `auth`/`unauth` parameterized by an `Enc` record (type-specific serialization), plus `ref-dig` to extract a digest from any reference:

```agda
record Enc (A : Set) : Set where
  field ser : A → Val ; des : Val → A

record Kit : Set₁ where
  field
    Ref     : Set → Set
    M       : Set → Set
    auth    : {A : Set} → Enc A → A → Ref A
    unauth  : {A : Set} → Enc A → Ref A → M A
    ref-dig : {A : Set} → Ref A → Digest
    ...
```

Each data structure provides an `Enc` instance that serializes one layer shallowly using `ref-dig` for children:

```agda
encBST : Enc (BST Ref)
encBST = record { ser = go ; des = decode }
  where
  go (leaf n)     = encode (inl n)
  go (node l k r) = encode (inr (ref-dig l , k , ref-dig r))  -- O(1)!
```

**ProverKit**: `Ref A = A × Digest`. `ref-dig = snd` extracts the cached digest in O(1), so `ser` never recurses into children. Each `unauth` emits one shallow encoding — O(log N) for a search path.

**VerifierKit**: `Ref A = Digest`. `unauth` pops from the proof stream and checks the hash.

## Collision extraction

The verifier produces a computation tree — a free monad of hash-checked lookups:

```agda
data Comp (R : Set) : Set where
  ret  : R → Comp R
  step : Digest → (Val → Comp R) → Comp R

extract : (c : Comp R) (s₁ s₂ : List Val)
  → run c s₁ ≡ ok r₁  → run c s₂ ≡ ok r₂  → r₁ ≠ r₂  → Collision
```

Induction on the tree: at each `step`, both streams provide `v₁, v₂` with `hash v₁ = d = hash v₂`. Either `v₁ ≠ v₂` (collision) or `v₁ = v₂` (recurse).

## Files

| File | Lines | Description |
|------|-------|-------------|
| `agda/AtkeyADS.agda` | 284 | **Main formalization.** Natural data types + efficient prover + collision extraction. Plain Agda, no sorry. |
| `agda/GenericADS.agda` | 286 | Earlier version with O(N) prover bug (parametric `encode` serializes entire subtrees). |
| `agda/EfficientADS.agda` | 313 | Fixes O(N) via polynomial functor codes, but loses natural data types. |
| `agda/AtkeyCorrectness.agda` | 388 | Atkey's parametricity claim (agda-bridges). Round-trip law critique. |

## Development

`AtkeyADS.agda`, `GenericADS.agda`, and `EfficientADS.agda` are plain Agda:

```bash
agda agda/AtkeyADS.agda
```

`AtkeyCorrectness.agda` requires a patched Agda with bridge types — see `agda-check`.

## References

- Miller, Hicks, Katz, Shi — [Authenticated Data Structures, Generically](https://amiller.github.io/lambda-auth/) (POPL 2014)
- Atkey — [Authenticated Data Structures, Generically](https://bentnib.org/posts/2016-04-12-authenticated-data-structures-as-a-library.html) (2016)
- Gregersen, Bowman et al. — [Authenticated Data Structures for Stateful Contracts](https://arxiv.org/abs/2501.10802) (2025)
