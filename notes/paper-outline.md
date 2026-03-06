# Paper Outline: Authenticated Data Structures, for Free
## ICFP Pearl

### Title options
- "Authenticated Data Structures, for Free" (riff on Wadler)
- "The Type Is the Proof: ADS Security via Internal Parametricity"

### Audience
PL researchers (ICFP). People who know free theorems. The pearl is: a real security property from a real system, proved by parametricity alone.

### Core claim
If an adversary fools the verifier into accepting a wrong result, we can constructively extract a collision in the hash function. This is the standard cryptographic reduction for ADS security, formalized as induction on the computation tree (free monad of hash-checked lookups). No assumption of hash injectivity — only collision resistance.

As a secondary contribution, we formalize Atkey's 2016 observation that parametricity over the auth kit guarantees correctness of honest computations (via agda-bridges). This is essentially a sanity check: honest programs compute the right answer.

### The story
Miller had the intuition in 2013: write ADS code polymorphic over an auth monad, get security from the types. But couldn't close the gap — unclear whether the type system actually *proves* the property or merely *expresses* the right shape. The POPL 2014 paper succeeded by going operational semantics instead. Atkey (2016) claimed the parametricity argument works. We formalize it, confirming the original intuition was right all along.

### Noether connection
Footnote or brief remark only. Atkey (POPL 2014) observed parametricity is Noether's theorem. Nice context, not the pearl's contribution.

---

## 1. Introduction

Miller et al. (POPL 2014) built authenticated data structures as a library. The original implementation (in Haskell) used a polymorphic "auth monad" interface — write the data structure once, instantiate with prover or verifier. The intuition: polymorphism over the auth interface should give security for free. But the paper couldn't close this gap. It wasn't clear whether the Haskell types actually *prove* the security property or just *express* the right shape. The POPL paper succeeded by an operational semantics approach instead.

Atkey (2016 blog post) revisited the library approach and claimed the security property follows from parametricity. Kmett built a Haskell library (Control.Monad.Auth) embodying this idea. But the claim was never formalized.

We formalize it using agda-bridges (internal parametricity for Cubical Agda).

**The punchline:** The type signature `f : ∀ kit → A → m A` *is* the security argument — the compiler checks it, and the free theorem is the proof. The original intuition was right.

## 2. Background

### 2.1 Authenticated data structures as a library
- Miller/Hicks/Katz/Shi POPL 2014 setup
- The AuthKit interface: m, au, ret, bind, auth, unauth
- Three implementations: Prover (Merkle state), Verifier (hash checking), Identity (no auth)
- The key insight: write code once, instantiate with different kits

### 2.2 Parametricity and free theorems
- Reynolds' abstraction theorem (brief)
- Wadler's "Theorems for free" (brief)
- The recipe: polymorphic type → relational interpretation → free theorem
- Example: `∀ X. X → X` must be identity

### 2.3 Internal parametricity and agda-bridges
- Cubical Agda + bridge types (Cavallo & Harper)
- The `param` primitive: extracts the free theorem as a proof term
- NRGraphs and DispNRGs: how to encode contexts and types
- Reference: Cagne, Lamiaux, Moeneclaey (the agda-bridges authors)

### 2.4 The Noether connection (optional — could be a remark)
- Atkey POPL 2014: parametricity IS Noether's theorem
- Type instantiations = coordinate transformations
- Free theorem = conservation law
- We don't need this for the formalization, but it's the conceptual frame

## 3. The Auth Kit, Formally

### 3.1 The interface
```
AuthKit = Σ (Type → Type) λ m →
  Σ (Type → Type) λ au →
    (∀ X → X → m X)                    -- ret
  × (∀ X Y → m X → (X → m Y) → m Y)   -- bind
  × (∀ X → X → au X)                   -- auth
  × (∀ X → au X → m X)                 -- unauth
```

### 3.2 The identity kit
```
IdKit = (id, id, λ x → x, λ x k → k x, λ x → x, λ x → x)
```

### 3.3 Lawful kits
Two laws suffice:
- Monad left identity: `bind (ret x) k ≡ k x`
- Auth roundtrip: `unauth (auth x) ≡ ret x`

### 3.4 The polymorphic program type
```
f : ∀ kit → A → m_kit A
```
(In the NRGraph encoding: `authCompDNRG`)

## 4. The Free Theorem

### 4.1 The purity relation
The logical relation between an arbitrary lawful kit and IdKit:
- For m: `R_m mx₀ x₁ := ∃ x₀. ret x₀ ≡ mx₀ ∧ R x₀ x₁` (mx₀ is "pure")
- For au: `R_au ax₀ x₁ := ∃ x₀. auth x₀ ≡ ax₀ ∧ R x₀ x₁`

### 4.2 Compatibility of operations
Show each kit operation respects the relation:
- ret: immediate (reflexivity)
- bind: uses monad left identity law
- auth: immediate
- unauth: uses auth roundtrip law

### 4.3 Theorem 1 (purity)
```
∀ kit (lawful) → ∀ x : A →
  f kit x ≡ ret_kit (f IdKit x)
```
The output is always "pure" — it's `ret` applied to the canonical value.

### 4.4 Corollary: Agreement
```
∀ kit₁ kit₂ (both lawful) → ∀ x : A →
  pure_value(f kit₁ x) ≡ pure_value(f kit₂ x)
```
Both equal `f IdKit x`. Prover and verifier agree.

## 5. Collision Extraction (the security theorem)

### 5.1 The computation tree
Model a verified computation as a free monad of hash-checked lookups:
```
data Comp R : Set where
  ret  : R → Comp R
  step : Digest → (Val → Comp R) → Comp R
```
Each `step d k` says: "give me a value `v` with `hash v = d`, then continue with `k v`." This is what `unauth` compiles to. The continuation captures the dependency of later digests on earlier values.

### 5.2 The verifier
```
run : Comp R → Stream → Outcome R
```
Consumes values from the proof stream, checks each hash, returns the result or fails.

### 5.3 Collision extraction theorem
```
extract : run c s₁ ≡ ok r₁ → run c s₂ ≡ ok r₂ → r₁ ≠ r₂ → Collision hash
```
By induction on the computation tree:
- `ret`: both return the same value — contradiction.
- `step d k`: both streams provide values `v₁, v₂` with `hash v₁ = d = hash v₂`.
  - `v₁ ≠ v₂`: collision found.
  - `v₁ = v₂`: both runs continue at the same tree node — recurse.

The collision lives at the **first divergence point**. Before that, everything is identical (same digests, same tree node). Self-contained, 129 lines, no library dependencies.

### 5.4 Connecting the layers
The honest prover runs `f ProverKit x`, producing result `r` and proof stream `π`. By correctness (Section 4), `r = f IdKit x`. If an adversary provides stream `π'` and the verifier accepts result `r' ≠ r`, the extraction theorem gives a collision.

## 6. Formalization of Correctness in Agda-Bridges

### 5.1 The NRGraph construction
- `Unit,m` → `Unit,m,au` → `AuthKitNRG`
- The TyCon pattern for type constructors
- De Bruijn indexing for variables (var0, var1, var2, ...)

### 5.2 Operation DispNRGs
- retDNRG, bindDNRG, authDNRG, unauthDNRG
- The inline record pattern (critical for Agda's unifier)
- Product encoding: `×Form`

### 5.3 The edge (purity relation)
- `edge-kit-Id` construction
- The m-relation and au-relation as Σ-types
- Compatibility proofs for each operation

### 5.4 Applying param
- `rawParam x = param AuthKitNRG authCompDNRG f (AuthKit→cr kit) (AuthKit→cr IdKit) edge-kit-Id x x refl`
- Extracting Theorem1 and the canonical form
- The agreement corollary: one line from Theorem1-witness

### 5.5 Simpler examples as warm-ups
- Identity: `∀ X → X → X` (graph-of-h trick, 3 lines)
- Noninterference: `∀ S → S → P → P` (total relation trick, 3 lines)
- These validate the approach before tackling the full AuthKit

## 7. Discussion

### 7.1 What the formalization reveals
- The collision extraction is surprisingly simple — pure induction on the free monad, no fancy machinery
- The key insight: at the first divergence point between two proof streams, both values pass the same hash check, giving the collision immediately
- The correctness layer (parametricity) is a sanity check; the two laws (monad left identity + auth roundtrip) are exactly what's needed
- The computation tree (free monad) cleanly separates the program structure from the proof stream, making the reduction transparent

### 7.2 The kit pattern (generalization)
- The same recipe applies beyond ADS: identify what code shouldn't depend on, make it abstract, get invariant for free
- Table of instances (noninterference, representation independence, effect abstraction, capability security)
- Each row is a "conservation law" in Atkey's sense

### 7.3 Practical implications
- For ADS library designers: the type signature is your security audit
- For compiler writers: parametricity-preserving compilation = security-preserving compilation
- For language designers: more parametricity = more free theorems = more security guarantees

### 7.4 Limitations
- The collision extraction assumes a fixed computation tree (the program doesn't branch on external input beyond the proof stream)
- Internal parametricity (for the correctness layer) requires Cubical Agda + bridges, which is not mainstream
- The formalization covers the core theorems but not a full ADS library (trees, maps, etc.)
- Monad laws are assumed as axioms, not derived from concrete implementations
- Collision resistance is assumed, not formalized as a computational hardness assumption (no probabilistic reasoning)

## 8. Related Work

- **Miller, Hicks, Katz, Shi (POPL 2014)**: the authenticated data structures as a library paper
- **Atkey (POPL 2014)**: "From Parametricity to Conservation Laws, via Noether's Theorem"
- **Atkey (2016 blog)**: "Authenticated Data Structures, Generically" — the claim we formalize
- **Kmett**: Control.Monad.Auth Haskell library
- **Reynolds (1983)**: Types, Abstraction and Parametric Polymorphism
- **Wadler (1989)**: Theorems for Free
- **Bernardy, Coquand, Moulin**: Internal parametricity
- **Cavallo, Harper**: Internal parametricity and cubical type theory
- **Cagne, Lamiaux, Moeneclaey**: agda-bridges (the tool we use)
- **VoigtlanderTheorems**: the bridgy-lib example we build on

## 9. Conclusion

The security of authenticated data structures is formalized as a collision extraction theorem: if an adversary's proof stream makes the verifier accept an incorrect result, we constructively produce a collision in the hash function. The proof is 129 lines of plain Agda, by induction on the computation tree, requiring no assumptions beyond collision resistance. We also formalize Atkey's 2016 claim that parametricity over the auth kit guarantees correctness (388 lines, Cubical Agda with agda-bridges).

---

## Easy bits to draft first
1. Section 5 (Collision Extraction) — the main result, clean and self-contained
2. Section 3 (Auth Kit) — directly from the Agda code
3. Section 4 (Free Theorem) — math is clean
4. Section 8 (Related Work) — list is known
5. The dictionary table (Section 7.2 or Introduction)

## Needs more thought
- How to position: the collision extraction is the real contribution, the parametricity is context
- Venue / format (ICFP pearl? CSF? Workshop?)
- Whether the Noether framing adds anything or is a distraction
- How much space to give the agda-bridges formalization (Section 6) vs the collision extraction (Section 5)
- How to present the NRGraph construction without losing readers (Section 6.1-6.2 is dense)
