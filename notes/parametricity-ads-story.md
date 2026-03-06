# Authenticated Data Structures, Free Theorems, and the Library Approach

## The Story

In 2012 I built [redblackmerkle](https://github.com/amiller/redblackmerkle) — a red-black Merkle tree where the balancing algorithms are written once against an abstract interface (`store`/`get`/`empty`), and different interpretations give you different roles:

- **Identity**: plain tree operations
- **Prover**: pairs values with hashes, emits a verification object
- **Verifier**: consumes the VO, checks hashes

The Haskell version used a typeclass (`RedBlackMonad`). The Python version used method dispatch. Both encoded the same idea: **parametricity over the storage abstraction forces the prover and verifier to agree**. The algorithms literally can't distinguish which interpretation they're running under, so if the prover accepts, the verifier must accept too (modulo hash collisions).

This was the parametricity argument, in code, before I had the vocabulary for it.

## POPL 2014: Two Papers, One Principle

At POPL 2014, two papers appeared that both exploited parametric polymorphism for correctness:

**Authenticated Data Structures, Generically** (Miller, Hicks, Katz, Shi) — my paper. We formalized the ADS construction in a custom language λ-auth with an abstract `auth` type. The compiler had a Prover mode and a Verifier mode. The correctness proof went through operational semantics — the traditional PL way.

**From Parametricity to Conservation Laws, via Noether's Theorem** (Atkey) — showed that if you encode a physical system as a polymorphic program in System Fω, the free theorem you get from the type IS Noether's theorem. Time-translation symmetry (parametricity over time) yields conservation of energy. Coordinate-translation symmetry yields conservation of momentum.

I saw Atkey present this at POPL. The parallel was immediate: both papers used parametricity to derive correctness properties "for free" from types. But the mechanisms looked different — one was operational semantics, the other was relational parametricity.

## The Dissatisfaction

I'd always preferred the typeclass/library approach. When Mike Hicks and I started working on the POPL paper, I came in with the Haskell typeclass encoding and an interest in PHOAS (Parametric Higher-Order Abstract Syntax, another technique that exploits parametricity for correctness). But Mike guided us toward the operational semantics approach — custom language, custom compiler, custom correctness proof. That's the standard PL methodology and it was the right call for a strong paper.

But it meant the parametricity argument — the thing I found most elegant — was implicit rather than the centerpiece. The correctness came from the operational semantics proof, not from a free theorem.

## Atkey Closes the Loop (2016)

Two years later, Atkey wrote [Authenticated Data Structures, as a Library, for Free!](https://bentnib.org/posts/2016-04-12-authenticated-data-structures-as-a-library.html). He showed:

1. The ADS construction works as a plain OCaml library — no custom compiler needed
2. The abstract module type (`AUTHENTIKIT`) provides the parametricity boundary
3. **The correctness proof should be an instance of a free theorem** from relational parametricity for higher kinds (his own System Fω parametricity result from CSL 2012)

He left the formal proof as a claim. But the claim was exactly what I'd intuited in 2012: the typeclass/module abstraction *is* the proof. Parametricity does all the work.

## Three Haskell Encodings

The Haskell community produced three implementations, each encoding the parametricity differently:

1. **Kmett's `auth` (Backpack version)** — uses GHC module signatures (`Auth.hsig`). The `Auth` type and `M` monad are abstract in the signature; `Prover` and `Verifier` modules provide implementations. Closest to ML-style abstraction / Atkey's OCaml approach.

2. **Kmett's `auth` (typeclass version)** — `MonadAuth` with associated type family `Auth m a`. Prover: `Auth Prover a = Proof a Hash`. Verifier: `Auth Verifier a = Verification Hash`. Closest to my original `redblackmerkle` typeclass design.

3. **Trail of Bits' `indurative`** — uses `DerivingVia` over sparse Merkle trees. `deriving Authenticate via Auth SHA3_256 (Map Int) String`. Most magical, least visible parametricity.

## The Meat: Why Does This Work?

The core mechanism is simple:

```
-- Write this once:
lookup :: MonadAuth m => Path -> Tree m a -> m (Maybe a)

-- Run it in two modes:
trust  :: (forall m. MonadAuth m => m a) -> (a, Certificate)
verify :: (forall m. MonadAuth m => m a) -> Certificate -> Maybe a
```

The `forall m` quantifier is the parametricity boundary. Any computation `forall m. MonadAuth m => m a` **must** work the same way regardless of whether `m` is `Prover` or `Verifier`. The only things it can do are `auth` and `unauth` — it can't inspect the representation of `Auth m a`.

The free theorem says: if the Prover produces a result `a` and a certificate `c`, and if the Verifier accepts `c`, then the Verifier must produce the same result `a`. This follows purely from the type — no operational semantics needed.

The same mechanism, in Atkey's Noether paper:

```
-- A Lagrangian invariant under time translation:
-- L : forall α. α → (Fin n → ℝ) → (Fin n → ℝ) → ℝ   (schematically)
-- The free theorem from the ∀α says L can't depend on α
-- → geometric invariance → Noether's theorem → energy conservation
```

Both are instances of: **parametric polymorphism constrains behavior, and those constraints are exactly the correctness properties you want**.

## What's Missing: Formal Support

Atkey's 2016 claim was never formally proved — until 2025. Ohlenbusch, Spies, and Birkedal published ["Logical Relations for Formally Verified Authenticated Data Structures"](https://iris-project.org/pdfs/2025-ccs-veriauth.pdf) at CCS 2025, mechanizing the argument in Iris/Rocq.

But the proof technique is still bespoke — they built a custom relational separation logic for collision-resistant hashing. What I'd really like to see is **generic support for free theorem reasoning** in proof assistants. Write a polymorphic library, derive the free theorem, get the correctness property. The pieces exist:

- **ParamCoq** / **Trocq** — parametricity translations for Rocq
- **Agda-bridges** (POPL 2024) — internal parametricity for Cubical Agda, one-liner free theorem proofs
- **Substructural Parametricity** (FSCD 2025) — even stronger guarantees in ordered/linear type systems

But nobody has yet built the tooling that says: "here's a library with an abstract type, here's the free theorem, here's your correctness proof." That would turn parametricity from a design intuition into a verification methodology.

## The Itch

The thing that's always fascinated me is that this is a *meta-property*. It's not a property of any particular program — it's a property of the type system itself, which gives you properties of all programs that inhabit certain types. You can't get this in Java (`instanceof` breaks it), you can't get it in Python (everything is inspectable), you can barely get it in Haskell (typeclasses approximate it, but `seq`, `unsafeCoerce`, and other escape hatches weaken it).

The promise of formalization is making this meta-property first-class: a proof assistant where "by parametricity" is a tactic, not a hand-wave.
