{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

-- Noninterference from parametricity: a function polymorphic over
-- a "secret" type can't use the secret to affect its public output.
--
-- This is Noether for programs, instance 2:
--   Symmetry:           any permutation of secrets
--   Conservation law:   output is constant in the secret
--   Conserved quantity:  f(Unit, tt, p) — the output at the trivial secret

module Bridgy.Examples.Noninterference where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.BDisc
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Param
open import Bridgy.ROTT.Rules
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

postulate
  l : Level
  P : Type l
  bdP : isBDisc P

-- The type: ∀ S → S → P → P
-- A function that receives a secret and a public value, returns public.
secretProcDNRG : DispNRG l (TypeNRG l)
secretProcDNRG = →Form l l X⊨ElX (→Form l l (bDisc-asDNRG P bdP) (bDisc-asDNRG P bdP))


------------------------------------------------------------------------
-- Noninterference: the output doesn't depend on the secret.
--
-- Proof: instantiate parametricity with the TOTAL relation on S
-- (everything relates to everything). Since f respects all relations,
-- it must give the same answer for any two secrets.

noninterference : (f : ∀ (S : Type l) → S → P → P)
  (S : Type l) (s₁ s₂ : S) (p : P) →
  f S s₁ p ≡ f S s₂ p
noninterference f S s₁ s₂ p =
  param (TypeNRG l) secretProcDNRG f
    S S (λ _ _ → Lift Unit)
    s₁ s₂ (lift tt)
    p p refl


------------------------------------------------------------------------
-- The conserved quantity: f at the trivial secret type.
-- This is the "energy" of the system — the output that's invariant
-- under all "coordinate changes" (secret type substitutions).

canonical : (f : ∀ (S : Type l) → S → P → P) → P → P
canonical f = f (Lift Unit) (lift tt)

canonical-eq : (f : ∀ (S : Type l) → S → P → P)
  (S : Type l) (s : S) (p : P) →
  f S s p ≡ canonical f p
canonical-eq f S s p =
  param (TypeNRG l) secretProcDNRG f
    S (Lift Unit) (λ _ _ → Lift Unit)
    s (lift tt) (lift tt)
    p p refl
