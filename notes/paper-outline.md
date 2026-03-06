# Paper Outline: Authenticated Data Structures, for Free
## ICFP Pearl

### Title options
- "Authenticated Data Structures, for Free" (riff on Wadler)
- "The Type Is the Proof: ADS Security via Internal Parametricity"

### Audience
PL researchers (ICFP). People who know free theorems. The pearl is: a real security property from a real system, proved by parametricity alone.

### Core claim
If a program is parametrically polymorphic over an "auth kit" interface, the security property (prover/verifier agreement) follows from the types alone — no separate proof needed. We formalize this in Cubical Agda using internal parametricity (agda-bridges), confirming Atkey's 2016 claim.

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

## 5. Formalization in Agda-Bridges

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

## 6. Discussion

### 6.1 What the formalization reveals
- The two laws (monad left identity + auth roundtrip) are exactly what's needed — no more
- The purity relation is the "right" logical relation (discovered through formalization, not assumed)
- The agreement corollary is trivial once purity is established

### 6.2 The kit pattern (generalization)
- The same recipe applies beyond ADS: identify what code shouldn't depend on, make it abstract, get invariant for free
- Table of instances (noninterference, representation independence, effect abstraction, capability security)
- Each row is a "conservation law" in Atkey's sense

### 6.3 Practical implications
- For ADS library designers: the type signature is your security audit
- For compiler writers: parametricity-preserving compilation = security-preserving compilation
- For language designers: more parametricity = more free theorems = more security guarantees

### 6.4 Limitations
- Internal parametricity requires Cubical Agda + bridges (not mainstream)
- The formalization covers the core theorem but not the full ADS library (trees, maps, etc.)
- Monad laws are assumed as axioms, not derived from implementations
- No treatment of computational effects beyond the monad interface

## 7. Related Work

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

## 8. Conclusion

Atkey's 2016 claim is now formally verified: the security of authenticated data structures — that any polymorphic program over the auth kit produces the same pure result regardless of implementation — follows from internal parametricity. The proof is 388 lines of Cubical Agda, uses no postulates beyond the bridge primitives, and confirms that the type signature alone is a sufficient security argument.

---

## Easy bits to draft first
1. Section 3 (Auth Kit) — directly from the Agda code
2. Section 4 (Free Theorem) — the math is clean and self-contained
3. Section 5.4-5.5 (param application + warm-ups) — concrete code
4. Section 7 (Related Work) — list is known
5. The dictionary table (Section 6.2 or Introduction)

## Needs more thought
- How much Noether framing in the intro (too much → distracting, too little → loses the hook)
- Venue / format (ICFP pearl? CSF? Workshop? Long-form essay?)
- Whether to include Track B material (capability security, sandboxes) — probably not, keep focused
- How to present the NRGraph construction without losing readers (Section 5.1-5.2 is dense)
