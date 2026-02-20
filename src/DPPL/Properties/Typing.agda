open import Lib.Algebra.Reals

module DPPL.Properties.Typing (R : Reals₀) where

open import DPPL.Regularity
open import DPPL.Syntax R renaming (_▸_ to _▹_)
open import DPPL.Typing R

open import Lib.Prelude
open import Lib.Data.Dec
open import Lib.Data.Vector
open import Lib.Data.Finset
open import Lib.LocallyNameless.Unfinite
open import Lib.LocallyNameless.BindingSignature
open import Lib.LocallyNameless.oc-Sets
open import Lib.LocallyNameless.AbstractionConcretion

open import Lib.Syntax.Env
open import Lib.Syntax.Substitution

open import Data.Bool.Order using (lift)
open import Data.Dec.Base
open import Data.Fin.Base
open import Data.Nat.Base using (Nat-is-set)
open import Data.Finset.Base

open SyntaxVars
open TypingVars
open FinsetSyntax
open LocalClosed
open Body

tsub-refl : T <: T
tsub-refl {treal c}        = sreal Reg↓≤.≤-refl
tsub-refl {_ ⇒[ _ , _ ] _} = sarr tsub-refl tsub-refl Reg↓≤.≤-refl Eff≤.≤-refl
tsub-refl {ttup _ ts}      = stup (λ i → tsub-refl)
tsub-refl {tdist T}        = sdist tsub-refl

∉-dom-fv :
  {x : 𝔸}
  (_ : Γ ⊢ t :[ e ] T)
  (_ : x ∉ dom Γ)
  → ------------------
  x ∉ fv t
∉-dom-fv (tsub Hty _ _) H∉      = ∉-dom-fv Hty H∉
∉-dom-fv (tpromote Hty _ H⊆) H∉ =
  ∉-dom-fv Hty (false→is-no λ H∈ → is-no→false H∉ (env-sub→dom-sub H⊆ _ H∈))
∉-dom-fv (tvar H∈) H∉ = ∉∷
  (false→is-no λ p → is-no→false H∉ (env-sub→dom-sub H∈ _ (hereₛ' (Id≃path.from p))))
  tt
∉-dom-fv {Γ = Γ} {x = x} (tlam {t = t} (Иi As Hty)) H∉ =
  let y , H∉y = fresh{𝔸} ([ x ] ∪ As)
      H∉' = ∉-dom-fv {x = x} (Hty y ⦃ ∉∷₂ H∉y ⦄)
        $ subst (_ ∉_) (sym $ dom-cons Γ) (∉∷ (sym≠ _ _ (∉∷₁ H∉y)) H∉)
  in ∉∪ (open-notin (t ₀) H∉') tt
∉-dom-fv (tapp {ts = ts} Hty Hty₁) H∉ = ∉⋃' (fv ∘ ts)
  $ Fin-cases (∉-dom-fv Hty H∉)
  $ Fin-cases (∉-dom-fv Hty₁ H∉) λ ()
∉-dom-fv (tprim {t = t} Hϕ Hty) H∉ = ∉⋃' (fv ∘ t) $ Fin-cases (∉-dom-fv Hty H∉) λ ()
∉-dom-fv treal H∉                  = tt
∉-dom-fv (ttup {ts = ts} Htys) H∉  = ∉⋃' (fv ∘ ts) λ i → ∉-dom-fv (Htys i) H∉
∉-dom-fv (tproj {t = t} i Hty) H∉  = ∉⋃' (fv ∘ t) $ Fin-cases (∉-dom-fv Hty H∉) λ ()
∉-dom-fv (tif {ts = ts} Hty Hty₁ Hty₂ H≤) H∉ = ∉⋃' (fv ∘ ts)
  $ Fin-cases (∉-dom-fv Hty H∉)
  $ Fin-cases (∉-dom-fv Hty₁ H∉)
  $ Fin-cases (∉-dom-fv Hty₂ H∉) λ ()
∉-dom-fv tuniform H∉ = tt
∉-dom-fv (tsample {t = t} Hty) H∉ = ∉⋃' (fv ∘ t) $ Fin-cases (∉-dom-fv Hty H∉) λ ()
∉-dom-fv (tweight {t = t} Hty) H∉ = ∉⋃' (fv ∘ t) $ Fin-cases (∉-dom-fv Hty H∉) λ ()
∉-dom-fv (tinfer {t = t} Hty) H∉  = ∉⋃' (fv ∘ t) $ Fin-cases (∉-dom-fv Hty H∉) λ ()
∉-dom-fv (tdiff {ts = ts} Hty Hty₁ Hty₂ Hc) H∉ = ∉⋃' (fv ∘ ts)
  $ Fin-cases (∉-dom-fv Hty H∉)
  $ Fin-cases (∉-dom-fv Hty₁ H∉)
  $ Fin-cases (∉-dom-fv Hty₂ H∉) λ ()
∉-dom-fv (tsolve {ts = ts} Hty Hty₁ Hty₂ Hc) H∉ = ∉⋃' (fv ∘ ts)
  $ Fin-cases (∉-dom-fv Hty H∉)
  $ Fin-cases (∉-dom-fv Hty₁ H∉)
  $ Fin-cases (∉-dom-fv Hty₂ H∉) λ ()

well-typed→lc : Γ ⊢ t :[ e ] T → lc-at 0 t
well-typed→lc (tsub Hty _ _)             = well-typed→lc Hty
well-typed→lc (tpromote Hty _ _)         = well-typed→lc Hty
well-typed→lc (tvar _)                   = lc-at-fvar
well-typed→lc (tlam {t = t} (Иi As Hty)) =
  let Hbody : body (t ₀)
      Hbody = Иi As λ x → lc-at→≻ _ _ $ well-typed→lc (Hty x)
  in lc-at-op $ Fin-cases (≻→lc-at _ _ $ body→1≻ _ Hbody) λ ()
well-typed→lc (tapp Hty Hty₁) = lc-at-op
  $ Fin-cases (well-typed→lc Hty)
  $ Fin-cases (well-typed→lc Hty₁) λ ()
well-typed→lc (tprim Hϕ Hty) = lc-at-op $ Fin-cases (well-typed→lc Hty) λ ()
well-typed→lc treal          = lc-at-op λ ()
well-typed→lc (ttup Htys)    = lc-at-op λ k → well-typed→lc (Htys k)
well-typed→lc (tproj i Hty)  = lc-at-op $ Fin-cases (well-typed→lc Hty) λ ()
well-typed→lc (tif Hty Hty₁ Hty₂ H≤) = lc-at-op
  $ Fin-cases (well-typed→lc Hty)
  $ Fin-cases (well-typed→lc Hty₁)
  $ Fin-cases (well-typed→lc Hty₂) λ ()
well-typed→lc tuniform      = lc-at-op λ ()
well-typed→lc (tsample Hty) = lc-at-op $ Fin-cases (well-typed→lc Hty) λ ()
well-typed→lc (tweight Hty) = lc-at-op $ Fin-cases (well-typed→lc Hty) λ ()
well-typed→lc (tinfer Hty)  = lc-at-op $ Fin-cases (well-typed→lc Hty) λ ()
well-typed→lc (tdiff Hty Hty₁ Hty₂ Hc) = lc-at-op
  $ Fin-cases (well-typed→lc Hty)
  $ Fin-cases (well-typed→lc Hty₁)
  $ Fin-cases (well-typed→lc Hty₂) λ ()
well-typed→lc (tsolve Hty Hty₁ Hty₂ Hc) = lc-at-op
  $ Fin-cases (well-typed→lc Hty)
  $ Fin-cases (well-typed→lc Hty₁)
  $ Fin-cases (well-typed→lc Hty₂) λ ()

weaken-typing : Γ ⊢ t :[ e ] T → Γ ⊆ Γ' → Γ' ⊢ t :[ e ] T
weaken-typing (tsub Hty H≤ H<:) H⊆     = tsub (weaken-typing Hty H⊆) H≤ H<:
weaken-typing (tpromote Hty H≤ H⊆') H⊆ = tpromote Hty H≤ (env-sub-trans H⊆' H⊆)
weaken-typing (tvar H∈) H⊆             = tvar (env-sub-trans H∈ H⊆)
weaken-typing {Γ' = Γ'} (tlam (Иi As Hty)) H⊆ = tlam $ Иi (As ∪ dom Γ') λ a →
  weaken-typing (Hty a ⦃ ∉∪₁ auto ⦄) (sub-cons' (∉∪₂ As auto) H⊆)
weaken-typing (tapp Hty Hty₁) H⊆ =
  tapp (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆)
weaken-typing (tprim Hϕ Hty) H⊆         = tprim Hϕ (weaken-typing Hty H⊆)
weaken-typing treal H⊆                  = treal
weaken-typing (ttup Htys) H⊆            = ttup λ i → weaken-typing (Htys i) H⊆
weaken-typing (tproj i Hty) H⊆          = tproj i (weaken-typing Hty H⊆)
weaken-typing (tif Hty Hty₁ Hty₂ H≤) H⊆ =
  tif (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆) (weaken-typing Hty₂ H⊆) H≤
weaken-typing tuniform H⊆                 = tuniform
weaken-typing (tsample Hty) H⊆            = tsample (weaken-typing Hty H⊆)
weaken-typing (tweight Hty) H⊆            = tweight (weaken-typing Hty H⊆)
weaken-typing (tinfer Hty) H⊆             = tinfer (weaken-typing Hty H⊆)
weaken-typing (tdiff Hty Hty₁ Hty₂ Hc) H⊆ =
  tdiff (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆) (weaken-typing Hty₂ H⊆) Hc
weaken-typing (tsolve Hty Hty₁ Hty₂ Hc) H⊆ =
  tsolve (weaken-typing Hty H⊆) (weaken-typing Hty₁ H⊆) (weaken-typing Hty₂ H⊆) Hc

tsub-env-refl : Γ <:ᵉ Γ
tsub-env-refl {Γ = ε}           = snil
tsub-env-refl {Γ = _ ▸ _ [ _ ]} = scons tsub-refl tsub-env-refl

tsub-env-dom : Γ' <:ᵉ Γ → dom Γ' ≡ dom Γ
tsub-env-dom snil                        = refl
tsub-env-dom (scons {Γ' = Γ'} {Γ} _ H<:) = ap ([ _ ] ∪_) (tsub-env-dom H<:)

scons' : T' <: T → Γ' <:ᵉ Γ → (Γ' , a ∶ T') <:ᵉ (Γ , a ∶ T)
scons' {Γ' = Γ'} {Γ} {a} H<: H<:ᵉ with holds? (a ∈ dom Γ') | holds? (a ∈ dom Γ)
... | yes _  | yes _  = H<:ᵉ
... | yes H∈ | no  H∉ = absurd (H∉ (subst (_ ∈ᶠˢ_) (tsub-env-dom H<:ᵉ) H∈))
... | no  H∉ | yes H∈ = absurd (H∉ (subst (_ ∈ᶠˢ_) (sym $ tsub-env-dom H<:ᵉ) H∈))
... | no  _  | no  _  = scons H<: H<:ᵉ

tsub-env-sub :
  {Γ₁ Γ₂ Γ₁' : TyEnv}
  (_ : Γ₂ <:ᵉ Γ₁)
  (_ : Γ₁' ⊆ Γ₁)
  → -------------------------------------
  Σ[ Γ₂' ∈ TyEnv ] Γ₂' <:ᵉ Γ₁' × Γ₂' ⊆ Γ₂
tsub-env-sub H<:ᵉ sub-nil = ε , snil , sub-nil'
tsub-env-sub (scons {T' = T'} H<: H<:ᵉ) (sub-cons {x = a , _} {H∉ = H∉} H⊆) =
  let Γ₂' , H<:' , H⊆' = tsub-env-sub H<:ᵉ H⊆
      H∉' : a ∉ dom Γ₂'
      H∉' = false→is-no (is-no→false H∉ ∘ subst (_ ∈ᶠˢ_) (tsub-env-dom H<:'))
  in
  (Γ₂' ▸ a , T' [ H∉' ]) , scons H<: H<:' , sub-cons H⊆'
tsub-env-sub (scons H<: H<:ᵉ) (sub-consr H⊆) =
  let Γ₂' , H<:' , H⊆' = tsub-env-sub H<:ᵉ H⊆ in
  Γ₂' , H<:' , sub-consr H⊆'

≤ᵗ-<:-trans :
  (_ : T ≤ᵗ c)
  (_ : T' <: T)
  → ------------
  T' ≤ᵗ c
≤ᵗ-<:-trans H≤ (sreal H≤')           = Reg↓≤.≤-trans H≤' H≤
≤ᵗ-<:-trans H≤ (stup H<:) i          = ≤ᵗ-<:-trans (H≤ i) (H<: i)
≤ᵗ-<:-trans H≤ (sarr H<: H<:₁ H≤' _) = Reg↓≤.≤-trans H≤' H≤
≤ᵗ-<:-trans H≤ (sdist _)             = tt

≤ᵉ-<:ᵉ-trans :
  (_ : Γ ≤ᵉ c)
  (_ : Γ' <:ᵉ Γ)
  → -------------
  Γ' ≤ᵉ c
≤ᵉ-<:ᵉ-trans H≤ (scons H<: H<:ᵉ) (sub-cons _) =
  ≤ᵗ-<:-trans (H≤ (sub-cons sub-nil')) H<:
≤ᵉ-<:ᵉ-trans H≤ (scons H<: H<:ᵉ) (sub-consr H∈) =
  ≤ᵉ-<:ᵉ-trans (H≤ ∘ sub-consr) H<:ᵉ H∈

tsub-env :
  (_ : Γ ⊢ t :[ e ] T)
  (_ : Γ' <:ᵉ Γ)
  → ---------------------
  Γ' ⊢ t :[ e ] T
tsub-env (tsub Hty H≤ H<:') H<: = tsub (tsub-env Hty H<:) H≤ H<:'
tsub-env (tpromote Hty H≤ H⊆) H<: with Γ₁' , H<:' , H⊆' ← tsub-env-sub H<: H⊆ =
  tpromote (tsub-env Hty H<:') (≤ᵉ-<:ᵉ-trans H≤ H<:') H⊆'
tsub-env (tvar H∈) H<: with _ , scons H<:' snil , H∈' ← tsub-env-sub H<: H∈ =
  tsub (tvar H∈') Eff≤.≤-refl H<:'
tsub-env (tlam (Иi As Hty)) H<: = tlam $ Иi As λ x → tsub-env (Hty x) (scons' tsub-refl H<:)
tsub-env (tapp Hty Hty₁) H<:    = tapp (tsub-env Hty H<:) (tsub-env Hty₁ H<:)
tsub-env (tprim Hϕ Hty) H<:     = tprim Hϕ (tsub-env Hty H<:)
tsub-env treal H<:              = treal
tsub-env (ttup Htys) H<:        = ttup λ i → tsub-env (Htys i) H<:
tsub-env (tproj i Hty) H<:      = tproj i (tsub-env Hty H<:)
tsub-env (tif Hty Hty₁ Hty₂ H≤) H<: =
  tif (tsub-env Hty H<:) (tsub-env Hty₁ H<:) (tsub-env Hty₂ H<:) H≤
tsub-env tuniform H<:                 = tuniform
tsub-env (tsample Hty) H<:            = tsample (tsub-env Hty H<:)
tsub-env (tweight Hty) H<:            = tweight (tsub-env Hty H<:)
tsub-env (tinfer Hty) H<:             = tinfer (tsub-env Hty H<:)
tsub-env (tdiff Hty Hty₁ Hty₂ Hc) H<: =
  tdiff (tsub-env Hty H<:) (tsub-env Hty₁ H<:) (tsub-env Hty₂ H<:) Hc
tsub-env (tsolve Hty Hty₁ Hty₂ Hc) H<: =
  tsolve (tsub-env Hty H<:) (tsub-env Hty₁ H<:) (tsub-env Hty₂ H<:) Hc

tlam-inv :
  {T₀ T₁ T₂ : Ty}
  {t : Tm ^ 1}
  (_ : Γ ⊢ lam T₀ ▹ t :[ e ] T)
  (_ : T ≡ᵢ T₁ ⇒[ c , e' ] T₂)
  → ---------------------------------------------
  И[ a ∈ 𝔸 ] Γ , a ∶ T₁ ⊢ conc (t ₀) a :[ e' ] T₂
tlam-inv (tlam Hlam) reflᵢ                              = Hlam
tlam-inv {Γ} (tsub Hty H≤ (sarr H<:₁ H<:₂ Hc He)) reflᵢ =
  let Иi As Hlam = tlam-inv Hty reflᵢ
  in  Иi As λ a →
    tsub-env (tsub (Hlam a) He H<:₂) (scons' {Γ' = Γ} H<:₁ tsub-env-refl)
tlam-inv {Γ} (tpromote {T = _ ⇒[ _ , _ ] _} Hty H≤ H⊆) reflᵢ =
  let Иi As Hlam = tlam-inv Hty reflᵢ
  in  Иi (As ∪ dom Γ) λ a ⦃ H∉ ⦄ →
    weaken-typing (Hlam a ⦃ ∉∪₁ H∉ ⦄) (sub-cons' (∉∪₂ As H∉) H⊆)

ttup-inv :
  {vs : Tm ^ n}
  {Ts : Ty ^ n}
  (_ : Γ ⊢ tup n ▹ vs :[ e ] T)
  (_ : T ≡ᵢ ttup n Ts)
  → ---------------------------
  ∀ i → Γ ⊢ vs i :[ e ] Ts i
ttup-inv (ttup Htys) Heq i = subst (_ ⊢ _ :[ _ ]_)
  (is-set→cast-pathp (Ty ^_) Nat-is-set (ap snd (ttup-inj (Id≃path.to Heq))) $ₚ i)
  (Htys i)
ttup-inv (tsub Hty H≤ (stup H<:)) reflᵢ i = tsub (ttup-inv Hty reflᵢ i) H≤ (H<: i)
ttup-inv (tpromote {T = ttup _ _} Hty H≤ H⊆) reflᵢ i =
  tpromote (ttup-inv Hty reflᵢ i) H≤ H⊆

tinfer-inv :
  {v : Tm ^ 1}
  (_ : Γ ⊢ infer ▹ v :[ e ] T)
  → T ≡ᵢ tdist T'
  → -----------------------------------
  Γ ⊢ v ₀ :[ e ] tunit ⇒[ M↓ , rnd ] T'
tinfer-inv (tinfer Hty) reflᵢ              = Hty
tinfer-inv (tsub Hty H≤ (sdist H<:)) reflᵢ =
  tsub (tinfer-inv Hty reflᵢ) H≤ (sarr tsub-refl H<: Reg↓≤.≤-refl Eff≤.≤-refl)
tinfer-inv (tpromote {T = tdist _} Hty H≤ H⊆) reflᵢ =
  weaken-typing (tinfer-inv Hty reflᵢ) H⊆

subst-pres-typing :
  {x : 𝔸}
  {t u : Tm}
  {T₁ T₂ : Ty}
  (_ : Γ' ≡ᵢ [ x ∶ T₂ ] & Γ)
  (_ : ε ⊢ u :[ det ] T₂)
  (_ : Γ' ⊢ t :[ e ] T₁)
  → --------------------------
  Γ ⊢ (x => u) t :[ e ] T₁
subst-pres-typing {Γ = Γ} {x = x} reflᵢ Hu (tvar {a = a} H∈) with x ≡? a
... | yes x≡a with sub-cons _ ←
  env-sub-strengthenr {Γ₂' = Γ} H∈ (λ a' → subst (a' ∈ᶠˢ_) (sym $ ap [_] x≡a)) =
  weaken-typing Hu sub-nil'
... | no x≠a = tvar $ env-sub-strengthenl H∈ λ _ H∈' → false→is-no $
  ∈ᶠˢ-split (λ where reflᵢ → ∈ᶠˢ-split (λ where reflᵢ → x≠a refl) ¬mem-[] H∈') ¬mem-[]
subst-pres-typing {Γ = Γ} {x = x} {u = u} {T₂ = T₂} reflᵢ Hu
  (tlam {T = T} {e} {T'} {t = t} (Иi As Hty)) = tlam $ Иi ([ x ] ∪ As) λ a ⦃ H∉ ⦄ →
  let Heq : (x => u)((0 ~> a) (t ₀)) ≡ (0 ~> a)((x => u) (t ₀))
      Heq = subst-open-comm (t ₀) (sym≠ a x (∉∷₁ H∉)) (lc-at→≻ _ _ $ well-typed→lc Hu)
  in subst (λ x → _ ⊢ x :[ _ ] _) Heq
     $ subst-pres-typing (Id≃path.from (&-cons-distr {Γ' = Γ})) Hu (Hty a ⦃ ∉∷₂ H∉ ⦄)
subst-pres-typing HΓ Hu (tapp Hty Hty₁) =
  tapp (subst-pres-typing HΓ Hu Hty) (subst-pres-typing HΓ Hu Hty₁)
subst-pres-typing HΓ Hu (tprim Hϕ Hty) = tprim Hϕ (subst-pres-typing HΓ Hu Hty)
subst-pres-typing HΓ Hu treal          = treal
subst-pres-typing HΓ Hu (ttup Htys)    = ttup λ i → subst-pres-typing HΓ Hu (Htys i)
subst-pres-typing HΓ Hu (tproj i Hty)  = tproj i (subst-pres-typing HΓ Hu Hty)
subst-pres-typing HΓ Hu (tif Hty Hty₁ Hty₂ H≤) = tif
  (subst-pres-typing HΓ Hu Hty)
  (subst-pres-typing HΓ Hu Hty₁)
  (subst-pres-typing HΓ Hu Hty₂)
  H≤
subst-pres-typing HΓ Hu tuniform      = tuniform
subst-pres-typing HΓ Hu (tsample Hty) = tsample (subst-pres-typing HΓ Hu Hty)
subst-pres-typing HΓ Hu (tweight Hty) = tweight (subst-pres-typing HΓ Hu Hty)
subst-pres-typing HΓ Hu (tinfer Hty)  = tinfer (subst-pres-typing HΓ Hu Hty)
subst-pres-typing HΓ Hu (tdiff Hty Hty₁ Hty₂ Hc) = tdiff
  (subst-pres-typing HΓ Hu Hty)
  (subst-pres-typing HΓ Hu Hty₁)
  (subst-pres-typing HΓ Hu Hty₂)
  Hc
subst-pres-typing HΓ Hu (tsolve Hty Hty₁ Hty₂ Hc) = tsolve
  (subst-pres-typing HΓ Hu Hty)
  (subst-pres-typing HΓ Hu Hty₁)
  (subst-pres-typing HΓ Hu Hty₂)
  Hc
subst-pres-typing HΓ Hu (tsub Hty H≤ H<:) = tsub (subst-pres-typing HΓ Hu Hty) H≤ H<:
subst-pres-typing {Γ = Γ} {x = x} reflᵢ Hu
  (tpromote {Γ = Γ'} Hty H≤ H⊆) with holds? (x ∈ dom Γ')
... | yes H∈ with Γ'' , p , H⊆' , Hdisj ←
  env-sub-&-diffl {Γ₂' = Γ}
    (λ _ → ∈ᶠˢ-split (λ where reflᵢ → H∈) (λ Hε → absurd (¬mem-[] Hε))) H⊆
  rewrite Id≃path.from p = tpromote
    (subst-pres-typing reflᵢ Hu Hty)
    (λ H∈ → H≤ (env-sub-trans H∈ (env-sub-weakenl env-sub-refl Hdisj)))
    H⊆'
... | no H∉ = tpromote
  (subst (_ ⊢_:[ _ ] _) (sym $ subst-fresh _ _ (∉-dom-fv Hty (false→is-no H∉))) Hty)
  H≤
  (env-sub-strengthenl H⊆ λ _ H∈ →
    false→is-no $ ∈ᶠˢ-split (λ where reflᵢ → H∉ H∈) ¬mem-[])

