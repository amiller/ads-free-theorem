{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

-- Two tiny free theorems from scratch, to build intuition for
-- how agda-bridges' internal parametricity works.
--
-- Key idea: `param` takes a polymorphic function and a *relation*
-- between two type instantiations, and proves the function
-- respects that relation. Choosing the relation to be the
-- *graph of a function h* gives classical free theorems.

module Bridgy.Examples.TinyFreeThms where

open import Bridgy.Core.BridgePrims
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Param
open import Bridgy.ROTT.Rules
open import Cubical.Foundations.Prelude


------------------------------------------------------------------------
-- Example 1: ∀ X → X → X  (the "Church Unit" type)
--
-- Any f of this type must satisfy:
--   h (f A a) ≡ f B (h a)
-- for all h : A → B.  In other words, f commutes with every function.
--
-- Proof: instantiate parametricity at the graph relation of h.
--   R a₀ b₀  :=  h a₀ ≡ b₀
-- Provide  (a, h a, refl) — i.e., a relates to h a by R.
-- Parametricity returns: R (f A a) (f B (h a)), which IS h(f A a) ≡ f B (h a).

idDNRG : ∀ l → DispNRG l (TypeNRG l)
idDNRG l = →Form l l X⊨ElX X⊨ElX

id-free-thm : ∀ {l} (f : ∀ (X : Type l) → X → X)
  (A B : Type l) (h : A → B) (a : A) →
  h (f A a) ≡ f B (h a)
id-free-thm {l} f A B h a =
  param (TypeNRG l) (idDNRG l) f A B (λ a₀ b₀ → h a₀ ≡ b₀)
    a (h a) refl


------------------------------------------------------------------------
-- Example 2: ∀ X → X → X → X  (the "Church Bool" type)
--
-- Any f of this type satisfies:
--   h (f A a₁ a₂) ≡ f B (h a₁) (h a₂)
--
-- Same trick: use graph-of-h as the relation, provide both inputs
-- with their refl proofs.

boolDNRG : ∀ l → DispNRG l (TypeNRG l)
boolDNRG l = →Form l l X⊨ElX (→Form l l X⊨ElX X⊨ElX)

bool-free-thm : ∀ {l} (f : ∀ (X : Type l) → X → X → X)
  (A B : Type l) (h : A → B) (a₁ a₂ : A) →
  h (f A a₁ a₂) ≡ f B (h a₁) (h a₂)
bool-free-thm {l} f A B h a₁ a₂ =
  param (TypeNRG l) (boolDNRG l) f A B (λ a₀ b₀ → h a₀ ≡ b₀)
    a₁ (h a₁) refl
    a₂ (h a₂) refl


------------------------------------------------------------------------
-- What just happened?
--
-- 1. We described the polymorphic type as a DispNRG over TypeNRG:
--      TypeNRG l  =  the NRGraph where carriers are types, edges are relations
--      →Form      =  function space former (builds relational interpretation automatically)
--      X⊨ElX      =  "the type variable X itself" as a displayed NRG
--
-- 2. We called `param`:
--      param Γ A f g₀ g₁ gg  :  A ⦅ f g₀ , f g₁ ⦆# gg
--
--    This says: f at g₀ and f at g₁ are related by the A-relation,
--    whenever g₀ and g₁ are related by gg in the context Γ.
--
-- 3. For →Form, the relation A ⦅ f₀ , f₁ ⦆# gg unfolds to:
--      ∀ a₀ a₁ → domain-rel a₀ a₁ → codomain-rel (f₀ a₀) (f₁ a₁)
--    So after `param`, we supply the domain arguments to get the conclusion.
--
-- 4. The graph-of-h trick: choosing  R a₀ b₀ := (h a₀ ≡ b₀)  turns the
--    abstract relational statement into a concrete equation about h.
--    This is Reynolds' abstraction theorem specialized to function graphs.
