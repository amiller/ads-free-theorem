{-# OPTIONS --cubical --guarded --bridges --no-fast-reduce #-}

------------------------------------------------------------------------
-- Free theorem for authenticated data structures
--
-- We show that any program polymorphic over an "auth monad" interface
-- must satisfy prover/verifier agreement: if the prover produces a
-- result and certificate, and the verifier accepts, they agree.
--
-- This is Atkey's 2016 claim ("Authenticated Data Structures, as a
-- Library, for Free!") made formal via internal parametricity.
--
-- Following: Miller/Hicks/Katz/Shi (POPL 2014), Atkey (2016 blog),
-- Kmett's Control.Monad.Auth, and the VoigtlanderTheorems example
-- from bridgy-lib.
------------------------------------------------------------------------

module Bridgy.Examples.AuthFreeThm where

open import Bridgy.Core.BridgePrims
open import Bridgy.Core.BDisc
open import Bridgy.Core.List
open import Bridgy.ROTT.Judgments
open import Bridgy.ROTT.Param
open import Bridgy.ROTT.Rules
open import Bridgy.ROTT.MoreVarRules

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

postulate
  l : Level
  A : Type l
  hasbA : isBDisc A


------------------------------------------------------------------------
-- The Auth interface as a Σ-type
--
-- An "auth kit" packages:
--   m      : Type → Type          (the monad)
--   au     : Type → Type          (the authenticated wrapper)
--   ret    : X → m X
--   bind   : m X → (X → m Y) → m Y
--   auth   : X → au X
--   unauth : au X → m X

AuthKit : Type (ℓ-suc l)
AuthKit = Σ (Type l → Type l) λ m →
  Σ (Type l → Type l) λ au →
      ((X : Type l) → X → m X)
    × ((X Y : Type l) → m X → (X → m Y) → m Y)
    × ((X : Type l) → X → au X)
    × ((X : Type l) → au X → m X)

kit-m : AuthKit → Type l → Type l
kit-m k = k .fst

kit-au : AuthKit → Type l → Type l
kit-au k = k .snd .fst

kit-ret : (k : AuthKit) → (X : Type l) → X → kit-m k X
kit-ret k = k .snd .snd .fst

kit-bind : (k : AuthKit) → (X Y : Type l) → kit-m k X → (X → kit-m k Y) → kit-m k Y
kit-bind k = k .snd .snd .snd .fst

kit-auth : (k : AuthKit) → (X : Type l) → X → kit-au k X
kit-auth k = k .snd .snd .snd .snd .fst

kit-unauth : (k : AuthKit) → (X : Type l) → kit-au k X → kit-m k X
kit-unauth k = k .snd .snd .snd .snd .snd

-- Identity kit: both m and au are the identity
IdKit : AuthKit
IdKit = (λ X → X) , (λ X → X) ,
  (λ X x → x) , (λ X Y x k → k x) ,
  (λ X x → x) , (λ X x → x)


------------------------------------------------------------------------
-- NRGraph construction
--
-- Following VoigtlanderTheorems exactly, but with two type constructors
-- (m and au) instead of one (κ).

-- Abbreviation for the "type constructor" displayed NRG
private
  TyCon : ∀ {ℓ} {Γ : NRGraph ℓ} → DispNRG (ℓ-suc l) Γ
  TyCon = →Form _ _ (UForm l) (UForm l)

-- Step 1: Context with m : Type → Type
Unit,m : NRGraph (ℓ-suc l)
Unit,m = topNRG # TyCon

-- Step 2: Add au : Type → Type (independent of m, hence wkn)
Unit,m,au : NRGraph (ℓ-suc l)
Unit,m,au = Unit,m # wkn TyCon

------------------------------------------------------------------------
-- Operation dNRGs over Unit,m,au
--
-- After ΠForm (UForm l), the context is Unit,m,au # (UForm l):
--   var0 = X : Type l
--   var1 = au : Type → Type    (via wkn TyCon from Unit,m,au)
--   var2 = m  : Type → Type    (via TyCon from Unit,m)
--
-- After two ΠForms, the context is Unit,m,au # (UForm l) # (UForm l):
--   var0 = Y, var1 = X, var2 = au, var3 = m

-- ret : (X : Type l) → X → m X
retDNRG : DispNRG (ℓ-suc l) Unit,m,au
retDNRG = ΠForm (UForm l)
  (→Form _ _
    -- X
    (El (let v = var0 Unit,m,au (UForm l)
    in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))
    -- m X
    (El (app (Unit,m,au # (UForm l)) (UForm l) (UForm l)
      (let v = var2 topNRG TyCon (wkn TyCon) (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
      (let v = var0 Unit,m,au (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))))

-- bind : (X Y : Type l) → m X → (X → m Y) → m Y
bindDNRG : DispNRG (ℓ-suc l) Unit,m,au
bindDNRG = ΠForm (UForm l) (ΠForm (UForm l)
  (→Form _ _
    -- m X
    (El (app _ (UForm l) (UForm l)
      (let v = var3 topNRG TyCon (wkn TyCon) (UForm l) (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
      (let v = var1 {Γ = Unit,m,au} (UForm l) (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })))
  (→Form _ _
    -- (X → m Y)
    (→Form _ _
      (El (let v = var1 {Γ = Unit,m,au} (UForm l) (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))
      (El (app ((Unit,m,au # (UForm l)) # (UForm l)) (UForm l) (UForm l)
        (let v = var3 topNRG TyCon (wkn TyCon) (UForm l) (UForm l)
        in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
        (let v = var0 (Unit,m,au # (UForm l)) (UForm l)
        in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))))
    -- m Y
    (El (app ((Unit,m,au # (UForm l)) # (UForm l)) (UForm l) (UForm l)
      (let v = var3 topNRG TyCon (wkn TyCon) (UForm l) (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
      (let v = var0 (Unit,m,au # (UForm l)) (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))))))

-- auth : (X : Type l) → X → au X
authDNRG : DispNRG (ℓ-suc l) Unit,m,au
authDNRG = ΠForm (UForm l)
  (→Form _ _
    -- X
    (El (let v = var0 Unit,m,au (UForm l)
    in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))
    -- au X
    (El (app (Unit,m,au # (UForm l)) (UForm l) (UForm l)
      (let v = var1 {Γ = Unit,m} (wkn TyCon) (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
      (let v = var0 Unit,m,au (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))))

-- unauth : (X : Type l) → au X → m X
unauthDNRG : DispNRG (ℓ-suc l) Unit,m,au
unauthDNRG = ΠForm (UForm l)
  (→Form _ _
    -- au X
    (El (app (Unit,m,au # (UForm l)) (UForm l) (UForm l)
      (let v = var1 {Γ = Unit,m} (wkn TyCon) (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
      (let v = var0 Unit,m,au (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })))
    -- m X
    (El (app (Unit,m,au # (UForm l)) (UForm l) (UForm l)
      (let v = var2 topNRG TyCon (wkn TyCon) (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
      (let v = var0 Unit,m,au (UForm l)
      in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ }))))

------------------------------------------------------------------------
-- AuthKitNRG: the full NRGraph for AuthKit

AuthKitNRG : NRGraph (ℓ-suc l)
AuthKitNRG = Unit,m,au #
  ×Form _ _ (×Form _ _ retDNRG bindDNRG)
             (×Form _ _ authDNRG unauthDNRG)

-- Conversion and projection helpers

AuthKit→cr : AuthKit → AuthKitNRG .nrg-cr
AuthKit→cr k = ((tt , kit-m k) , kit-au k) ,
  ((kit-ret k , kit-bind k) , (kit-auth k , kit-unauth k))

NRGm : AuthKitNRG .nrg-cr → Type l → Type l
NRGm k = k .fst .fst .snd

NRGau : AuthKitNRG .nrg-cr → Type l → Type l
NRGau k = k .fst .snd

NRGret : (k : AuthKitNRG .nrg-cr) → (X : Type l) → X → NRGm k X
NRGret k = k .snd .fst .fst

NRGbind : (k : AuthKitNRG .nrg-cr) → (X Y : Type l) → NRGm k X → (X → NRGm k Y) → NRGm k Y
NRGbind k = k .snd .fst .snd

NRGauth : (k : AuthKitNRG .nrg-cr) → (X : Type l) → X → NRGau k X
NRGauth k = k .snd .snd .fst

NRGunauth : (k : AuthKitNRG .nrg-cr) → (X : Type l) → NRGau k X → NRGm k X
NRGunauth k = k .snd .snd .snd

------------------------------------------------------------------------
-- Displayed NRG for the polymorphic program type: A → m A
--
-- This represents the type of computations like:
--   roundtrip : ∀ kit → A → m A
--   roundtrip kit x = unauth (auth x)
--
-- or more complex authenticated operations like tree lookups.

authCompDNRG : DispNRG l AuthKitNRG
authCompDNRG = wkn (→Form _ _
  -- domain: A (bridge-discrete, constant across kits)
  (bDisc-asDNRG A hasbA)
  -- codomain: m A
  (El (app Unit,m,au (UForm l) (UForm l)
    (let v = var1 {Γ = topNRG} TyCon (wkn TyCon)
    in record { tm0 = v .tm0 ; tm1 = v .tm1 ; tm-nativ = v .tm-nativ })
    (code (bDisc-asDNRG A hasbA)))))


------------------------------------------------------------------------
-- Theorem 1: Purity preservation (analogous to Voigtlander Theorem 1)
--
-- If f : ∀ kit → A → m A is parametrically polymorphic, and we run it
-- with a kit satisfying:
--   (1) monad left-identity: bind (ret x) k ≡ k x
--   (2) auth roundtrip:      unauth (auth x) ≡ ret x
-- then the output is "pure": f kit x ≡ ret a for some a.
--
-- Specializing: Prover and Verifier both satisfy these laws,
-- so both produce pure results → they agree.

module theorem1
  (f : ∀ (k : AuthKitNRG .nrg-cr) → A → NRGm k A)
  (kit : AuthKit)
  -- Monad left-identity law (needed for bind compatibility)
  (law-bind : ∀ (X Y : Type l) (x : X) (k : X → kit-m kit Y) →
    kit-bind kit X Y (kit-ret kit X x) k ≡ k x)
  -- Auth roundtrip law (needed for unauth compatibility)
  (law-auth : ∀ (X : Type l) (x : X) →
    kit-unauth kit X (kit-auth kit X x) ≡ kit-ret kit X x)
  where

  -- A value is "pure" when it equals ret of some underlying value
  pureval : kit-m kit A → Type l
  pureval ma = Σ A (λ a → ma ≡ kit-ret kit A a)

  -- Logical relation between kit and IdKit
  --
  -- For m: κx0 ∈ m_kit X₀ relates to x₁ ∈ X₁ when
  --   ∃ x₀. ret x₀ ≡ κx₀ ∧ X₀X₁ x₀ x₁
  -- (i.e., κx₀ is a "pure" computation returning something related to x₁)
  --
  -- For au: ax0 ∈ au_kit X₀ relates to x₁ ∈ X₁ when
  --   ∃ x₀. auth x₀ ≡ ax₀ ∧ X₀X₁ x₀ x₁
  -- (i.e., ax₀ is the authentication of something related to x₁)

  edge-kit-Id : AuthKitNRG .nedge (AuthKit→cr kit) (AuthKit→cr IdKit)
  edge-kit-Id =
    -- NRG part: (Unit,m,au edge)
    -- This consists of: Unit edge, m-relation, au-relation
    ((tt ,
      -- m-relation: relates m_kit X₀ to X₁
      λ X0 X1 XX mx0 x1 → Σ X0 (λ x0 → (kit-ret kit X0 x0 ≡ mx0) × (XX x0 x1))) ,
      -- au-relation: relates au_kit X₀ to X₁
      λ X0 X1 XX ax0 x1 → Σ X0 (λ x0 → (kit-auth kit X0 x0 ≡ ax0) × (XX x0 x1)))
    ,
    -- Operations part: ((ret-compat, bind-compat), (auth-compat, unauth-compat))
    (
    -- ret compatibility: ret x0 relates to x1 when x0 relates to x1
    (λ X0 X1 XX x0 x1 xx → x0 , refl , xx)
    ,
    -- bind compatibility
    λ X0 X1 XX Y0 Y1 YY mx0 x1 hyp k0 k1 hypk →
      let
        hypk-fwd : Σ Y0 (λ y0 → (kit-ret kit Y0 y0 ≡ k0 (hyp .fst)) × YY y0 (k1 x1))
        hypk-fwd = hypk (hyp .fst) x1 (hyp .snd .snd)

        dedct1 : kit-ret kit X0 (hyp .fst) ≡ mx0
        dedct1 = hyp .snd .fst
      in
      hypk-fwd .fst ,
      ((hypk-fwd .snd .fst) ∙ (sym (law-bind X0 Y0 (hyp .fst) k0)))
      ∙ cong (λ blank → kit-bind kit X0 Y0 blank k0) dedct1 ,
      hypk-fwd .snd .snd
    ) ,
    (
    -- auth compatibility: auth x0 relates to x1 when x0 relates to x1
    (λ X0 X1 XX x0 x1 xx → x0 , refl , xx)
    ,
    -- unauth compatibility: if ax0 relates to x1 (via auth), then
    -- unauth ax0 relates to x1 (via ret), using the roundtrip law
    λ X0 X1 XX ax0 x1 hyp →
      let
        x0 = hyp .fst
        auth-eq : kit-auth kit X0 x0 ≡ ax0
        auth-eq = hyp .snd .fst
        xx : XX x0 x1
        xx = hyp .snd .snd

        roundtrip : kit-unauth kit X0 (kit-auth kit X0 x0) ≡ kit-ret kit X0 x0
        roundtrip = law-auth X0 x0
      in
      x0 , sym (sym (cong (kit-unauth kit X0) auth-eq) ∙ roundtrip) , xx
    )

  -- Raw parametricity output (private — used by Theorem1 and its corollaries)
  private
    rawParam : ∀ (x : A) → _
    rawParam x = param AuthKitNRG authCompDNRG f
      (AuthKit→cr kit) (AuthKit→cr IdKit) edge-kit-Id
      x x refl

  -- The theorem: for any input x, the output of f is pure
  Theorem1 : ∀ (x : A) → pureval (f (AuthKit→cr kit) x)
  Theorem1 x = rawParam x .fst , sym (rawParam x .snd .fst)

  -- The pure value IS f IdKit x (the "canonical" computation)
  Theorem1-witness : ∀ (x : A) → Theorem1 x .fst ≡ f (AuthKit→cr IdKit) x
  Theorem1-witness x = rawParam x .snd .snd

  -- Canonical form: f kit x ≡ ret (f IdKit x)
  Theorem1-canonical : ∀ (x : A) →
    f (AuthKit→cr kit) x ≡ kit-ret kit A (f (AuthKit→cr IdKit) x)
  Theorem1-canonical x =
    Theorem1 x .snd ∙ cong (kit-ret kit A) (Theorem1-witness x)


------------------------------------------------------------------------
-- Corollary: Prover/Verifier agreement
--
-- For ANY two kits satisfying the laws, the underlying pure values
-- agree: both equal f IdKit x.
--
-- This is the ADS security property: a polymorphic program that
-- type-checks against the auth interface MUST produce the same
-- answer regardless of which kit implements it.

module agreement
  (f : ∀ (k : AuthKitNRG .nrg-cr) → A → NRGm k A)
  (kit₁ : AuthKit)
  (law-bind₁ : ∀ (X Y : Type l) (x : X) (k : X → kit-m kit₁ Y) →
    kit-bind kit₁ X Y (kit-ret kit₁ X x) k ≡ k x)
  (law-auth₁ : ∀ (X : Type l) (x : X) →
    kit-unauth kit₁ X (kit-auth kit₁ X x) ≡ kit-ret kit₁ X x)
  (kit₂ : AuthKit)
  (law-bind₂ : ∀ (X Y : Type l) (x : X) (k : X → kit-m kit₂ Y) →
    kit-bind kit₂ X Y (kit-ret kit₂ X x) k ≡ k x)
  (law-auth₂ : ∀ (X : Type l) (x : X) →
    kit-unauth kit₂ X (kit-auth kit₂ X x) ≡ kit-ret kit₂ X x)
  where

  private
    module T₁ = theorem1 f kit₁ law-bind₁ law-auth₁
    module T₂ = theorem1 f kit₂ law-bind₂ law-auth₂

  -- The pure values agree: both are f IdKit x
  values-agree : ∀ (x : A) → T₁.Theorem1 x .fst ≡ T₂.Theorem1 x .fst
  values-agree x = T₁.Theorem1-witness x ∙ sym (T₂.Theorem1-witness x)

  -- Equivalent statement using canonical form:
  -- f kit₁ x = ret₁ a  and  f kit₂ x = ret₂ a  for the same a = f IdKit x
  canonical₁ : ∀ (x : A) →
    f (AuthKit→cr kit₁) x ≡ kit-ret kit₁ A (f (AuthKit→cr IdKit) x)
  canonical₁ = T₁.Theorem1-canonical

  canonical₂ : ∀ (x : A) →
    f (AuthKit→cr kit₂) x ≡ kit-ret kit₂ A (f (AuthKit→cr IdKit) x)
  canonical₂ = T₂.Theorem1-canonical
