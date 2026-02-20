open import Lib.Algebra.Reals

module DPPL.Typing (R : Reals₀) where

open import DPPL.Syntax R
open import DPPL.Regularity

open import Lib.Prelude
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.AbstractionConcretion
open import Lib.LocallyNameless.BindingSignature
open import Lib.Data.Vector
open import Lib.Syntax.Env

open import Order.Base
open import Order.Lattice

open VecSyntax
open VectorSyntax using () renaming (_∷_ to _∷ᵛ_)
open Reg↓≤ renaming (_≤_ to _≤reg_)
open Eff≤  renaming (_≤_ to _≤eff_)
open is-lattice Reg↓-lattice

TyEnv : Type
TyEnv = Env Ty

module TypingVars where
  variable
    Γ Γ' : TyEnv
    a    : 𝔸

open SyntaxVars
open TypingVars

PrimTy : (ϕ : Prim) → Coeff ^ PrimAr ϕ × Coeff
PrimTy padd    = make A↓ , A↓
PrimTy pmul    = make A↓ , A↓
PrimTy psin    = make A↓ , A↓
PrimTy pnormal = make M↓ , M↓
PrimTy pgamma  = make M↓ , M↓
PrimTy pwiener = lookup (M↓ ∷ C↓ ∷ []) , C↓

infix 5 _<:_
data _<:_ : Ty → Ty → Type where

  sreal :
    (_ : c ≤reg c')
    → -----------------
    treal c <: treal c'

  stup :
    {Ts Ts' : Ty ^ n}
    (_ : ∀ i → Ts i <: Ts' i)
    → -----------------------
    ttup n Ts <: ttup n Ts'

  sarr :
    {T₁ T₁' T₂ T₂' : Ty}
    (_ : T₁' <: T₁)
    (_ : T₂ <: T₂')
    (_ : c ≤reg c')
    (_ : e ≤eff e')
    → --------------------------------------
    T₁ ⇒[ c , e ] T₂ <: T₁' ⇒[ c' , e' ] T₂'

  sdist :
    (_ : T <: T')
    → -----------------
    tdist T <: tdist T'


data _<:ᵉ_ : TyEnv → TyEnv → Type where
  snil  : ε <:ᵉ ε
  scons
    : {H∉' : a ∉ dom Γ'} {H∉ : a ∉ dom Γ}
    → T' <: T → Γ' <:ᵉ Γ → (Γ' ▸ (a , T') [ H∉' ]) <:ᵉ (Γ ▸ (a , T) [ H∉ ])

_≤ᵉ_ : TyEnv → Coeff → Type
Γ ≤ᵉ c = ∀ {a T} → a ∶ T ∈ Γ → T ≤ᵗ c


infix 4 _⊢_:[_]_
data _⊢_:[_]_ : TyEnv → Tm → Eff → Ty → Type where

  tsub :
    (_ : Γ ⊢ t :[ e ] T)
    (_ : e ≤eff e')
    (_ : T <: T')
    → ------------------
    Γ ⊢ t :[ e' ] T'

  tpromote :
    (_ : Γ ⊢ t :[ e ] T)
    (_ : Γ ≤ᵉ c)
    (_ : Γ ⊆ Γ')
    → ------------------
    Γ' ⊢ t :[ e ] c ∩ᵗ T

  tvar :
    (_ : a ∶ T ∈ Γ)
    → -------------------
    Γ ⊢ fvar a :[ det ] T

  tlam :
    {t : Tm ^ 1}
    (_ : И[ a ∈ 𝔸 ] (Γ , a ∶ T) ⊢ conc (t ₀) a :[ e ] T')
    → ---------------------------------------------------
    Γ ⊢ lam T ▸ t :[ det ] T ⇒[ A↓ , e ] T'

  tapp :
    {ts : Tm ^ 2}
    (_ : Γ ⊢ ts ₀ :[ e ] T ⇒[ A↓ , e ] T')
    (_ : Γ ⊢ ts ₁ :[ e ] T)
    → ------------------------------------
    Γ ⊢ app ▸ ts :[ e ] T'

  tprim :
    {cs : Coeff ^ PrimAr ϕ}
    {t : Tm ^ 1}
    (_ : PrimTy ϕ ≡ (cs , c))
    (_ : Γ ⊢ t ₀ :[ e ] treals _ cs)
    → ------------------------------
    Γ ⊢ prim ϕ ▸ t :[ e ] treal c

  treal :
    {t : Tm ^ 0}
    → -------------------------------
    Γ ⊢ oreal r ▸ t :[ det ] treal A↓

  ttup :
    {Ts : Ty ^ n}
    {ts : Tm ^ n}
    (_ : ∀ i → Γ ⊢ ts i :[ e ] Ts i)
    → ------------------------------
    Γ ⊢ tup n ▸ ts :[ e ] ttup n Ts

  tproj :
    {Ts : Ty ^ n}
    {t : Tm ^ 1}
    (i : Fin n)
    (_ : Γ ⊢ t ₀ :[ e ] ttup n Ts)
    → --------------------------------
    Γ ⊢ proj n i ▸ t :[ e ] Ts i

  tif :
    {cs : Coeff ^ n}
    {ts : Tm ^ 3}
    (_ : Γ ⊢ ts ₀ :[ e ] treal P↓)
    (_ : Γ ⊢ ts ₁ :[ e ] treals n cs)
    (_ : Γ ⊢ ts ₂ :[ e ] treals n cs)
    (_ : ∀ i → P↓ ≤reg cs i)
    → -------------------------------
    Γ ⊢ if ▸ ts :[ e ] treals n cs

  tuniform :
    {t : Tm ^ 0}
    → --------------------------------
    Γ ⊢ ouniform ▸ t :[ rnd ] treal M↓

  tsample :
    {t : Tm ^ 1}
    (_ : Γ ⊢ t ₀ :[ rnd ] tdist T)
    → ----------------------------
    Γ ⊢ sample ▸ t :[ rnd ] T

  tweight :
    {t : Tm ^ 1}
    (_ : Γ ⊢ t ₀ :[ rnd ] treal M↓)
    → -----------------------------
    Γ ⊢ weight ▸ t :[ rnd ] tunit

  tinfer :
    {t : Tm ^ 1}
    (_ : Γ ⊢ t ₀ :[ e ] tunit ⇒[ M↓ , rnd ] T)
    → ----------------------------------------
    Γ ⊢ infer ▸ t :[ e ] tdist T

  tdiff :
    {ts : Tm ^ 3}
    (_ : Γ ⊢ ts ₀ :[ e ] treals m (make c) ⇒[ P↓ , det ] treals n (make c))
    (_ : Γ ⊢ ts ₁ :[ e ] treals m (make c))
    (_ : Γ ⊢ ts ₂ :[ e ] treals m (make A↓))
    (_ : c ≡ A↓ ⊎ c ≡ P↓)
    → ---------------------------------------------------------------------
    Γ ⊢ diff ▸ ts :[ e ] treals n (make A↓)

  tsolve :
    {ts : Tm ^ 3}
    (_ : Γ ⊢ ts ₀ :[ e ] treals (1 + n) (c ∷ᵛ make A↓) ⇒[ C↓ , det ] treals n (make A↓))
    (_ : Γ ⊢ ts ₁ :[ e ] treals (1 + n) (c ∷ᵛ make A↓))
    (_ : Γ ⊢ ts ₂ :[ e ] treal (c ∩ PC↓))
    (_ : c ≡ A↓ ⊎ c ≡ C↓)
    → ----------------------------------------------------------------------------------
    Γ ⊢ solve ▸ ts :[ e ] treals (1 + n) (make A↓)
