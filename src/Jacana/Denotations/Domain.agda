open import 1Lab.Type.Sigma

open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Exponential
open import Cat.Functor.Naturality
open import Cat.Displayed.Total
open import Cat.Cartesian
open import Cat.Prelude

open import Data.Fin.Base hiding (_≤_)

open import Jacana.Denotations.Regularity
open import Jacana.Regularity hiding (A)

open import Lib.Algebra.Reals
open import Lib.Homotopy.Join
open import Lib.Cat.Concrete
open import Lib.Data.Vector
open import Lib.Cat.Thin

open import Order.Diagram.Meet
open import Order.Base

import Jacana.Denotations.Site as Site
import Jacana.Syntax as Syntax

module Jacana.Denotations.Domain (R : Reals₀) (Ax : RegAssumptions R) where

open RegAssumptions Ax
open Reg⊆-lat hiding (top ; !)
open Functor
open Syntax R
open SyntaxVars
open _=>_
open Site R Ax
open Conc-category ℛ-conc
open Conc-psh ℛ-conc
open Repr-conc (λ x → ℛ-const x , refl)
open CPSh-on
open Reals R using (ℝ)
open Reg≤
open ∫Hom

𝔇 : Precategory _ _
𝔇 = CPSh

module 𝔇 = Precategory 𝔇

𝔇-cartesian : Cartesian-category 𝔇
𝔇-cartesian = CPSh-cartesian

𝔇-closed : Cartesian-closed 𝔇 𝔇-cartesian
𝔇-closed = CPSh-closed

open Cartesian-category 𝔇-cartesian hiding (⟨_,_⟩)
open Cartesian-closed 𝔇-closed using () renaming ([_,_] to _⇒_)
open Inverses

𝔇-ip : ∀ {n} → has-products-indexed-by 𝔇 (Fin n)
𝔇-ip = CPSh-ip

module 𝔇-ip {n} (F : 𝔇.Ob ^ n) = Indexed-product (𝔇-ip F)

□⟨_⟩₀ : Reg⊆ → ⌞ 𝔇 ⌟ → ⌞ 𝔇 ⌟
□⟨ X ⟩₀ A .fst = A .fst
□⟨ X ⟩₀ A .snd = cpsh module □⟨_⟩ where
  has-factor : ∀ U → (f : ∣ U ∣ₒ → ⌞ A ⌟) → Type
  has-factor U f =
    Σ[ V ∈ ℛ.Ob ] V .snd ∈ X × U .snd ≤ V .snd ×
    Σ[ g ∈ ∫ₚ ⟨ U .snd ⟩-reg ] Σ[ f' ∈ ∫ₚ (A .snd .is-sec V) ]
    f ≡ f' .fst ⊙ g .fst

  cpsh : CPSh-on ⌞ A ⌟
  cpsh .is-sec U f       = el (□ (has-factor U f) ∗ ∣ is-const f ∣) (hlevel 1)
  cpsh .is-sec-∘ f h Hf₀ = case h .snd of λ where
    (inr H⋆)        → case H⋆ of λ x p → inr (inc (_ , ap (f ⊙_) p))
    (inl (H≤ , Hh)) → case Hf₀ of λ where
      (inr H⋆) → case H⋆ of λ x p → inr (inc (_ , ap (_⊙ ∣ h ∣ₕ) p))
      (inl Hf) → inl $ flip □-map Hf λ (W , HW , V≤W , (g , Hg) , f' , p) →
        ( W
        , HW
        , ≤-trans H≤ V≤W
        , (g ⊙ ∣ h ∣ₕ , ∘-reg (⊆-reg H≤ g Hg) Hh)
        , f'
        , ap (_⊙ ∣ h ∣ₕ) p
        )
  cpsh .pt-sec x = inr (inc (_ , refl))

□⟨_⟩ : Reg⊆ → Functor 𝔇 𝔇
□⟨ X ⟩ .F₀                        = □⟨ X ⟩₀
□⟨ X ⟩ .F₁ f .fst                 = f .fst
□⟨ X ⟩ .F₁ (∫hom f Hf) .snd g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → case H⋆ of λ x p → inr (inc (_ , ap (f ⊙_) p))
  (inl Hg) → inl $ flip □-map Hg λ (W , HW , V≤W , h , (g' , Hg') , p) →
    W , HW , V≤W , h , (f ⊙ g' , Hf g' Hg') , ap (f ⊙_) p
□⟨ X ⟩ .F-id    = ext λ _ → refl
□⟨ X ⟩ .F-∘ f g = ext λ _ → refl

□-counit : □⟨ X ⟩ => Id
□-counit .η A .fst x     = x
□-counit .η A .snd g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → case H⋆ of λ x p → const-sec A p
  (inl Hg) → flip (□-elim (λ _ → hlevel 1)) Hg λ (W , HW , H≤ , h , g' , p) →
    subst (λ x → ∣ A .snd .is-sec _ x ∣) (sym p)
      (A .snd .is-sec-∘ _ (h .fst , inl (H≤ , h .snd)) (g' .snd))
□-counit .is-natural _ _ _ = ext λ _ → refl

□-comult : □⟨ X ∩ X' ⟩ => □⟨ X ⟩ F∘ □⟨ X' ⟩
□-comult .η A .fst x     = x
□-comult .η A .snd g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → case H⋆ of λ x p → inr (inc (_ , p))
  (inl Hg) → inl $ flip □-map Hg λ (W , HW , H≤ , h , g' , p) →
    ( W
    , HW .fst
    , H≤
    , h
    , (_ , inl (inc (W , HW .snd , ≤-refl , ((λ x → x) , id-reg) , g' , refl)))
    , p
    )
□-comult .is-natural _ _ _ = ext λ _ → refl

□-comult' : X ~ʳ X' → □⟨ X ⟩ F∘ □⟨ X' ⟩ => □⟨ X ∩ X' ⟩
□-comult' H~ .η A .fst x = x
□-comult' {X} {X'} H~ .η A .snd {U} g Hg₀ = case Hg₀ of λ where
  (inr H⋆)  → inr H⋆
  (inl Hg₁) → flip (□-elim (λ _ → hlevel 1)) Hg₁ λ (W1 , HW1 , H≤1 , h1 , g1 , p1) →
    case g1 .snd of λ where
      (inr H⋆)  → case H⋆ of λ x p → inr (inc (_ , p1 ∙ ap (_⊙ h1 .fst) p))
      (inl Hg₂) →
        flip (□-elim (λ _ → hlevel 1)) Hg₂ λ (W2 , HW2 , H≤2 , h2 , g2 , p2) →
        case H~ (_ , HW1) (_ , HW2) of λ H∩ →
        flip (∥-∥-elim (λ _ → hlevel 1)) (H∩ H≤2) λ ((z , Hz) , x≤z , z≤y) →
        let fac = inc
              ( (W2 .fst , z)
              , Hz
              , ≤-trans H≤1 x≤z
              , ((h2 .fst ⊙ h1 .fst) , ∘-reg (⊆-reg H≤1 _ (h2 .snd)) (h1 .snd))
              , (g2 .fst , A .snd .is-sec-∘ _ (ℛ-id≤ z≤y) (g2 .snd))
              , p1 ∙ ap (_⊙ h1 .fst) p2
              )
        in
        inl fac
□-comult' H~ .is-natural _ _ _ = ext λ _ → refl

□-comult-≅ : X ~ʳ X' → □⟨ X ∩ X' ⟩ ≅ⁿ □⟨ X ⟩ F∘ □⟨ X' ⟩
□-comult-≅ HX .to             = □-comult
□-comult-≅ HX .from           = □-comult' HX
□-comult-≅ HX .inverses .invl = ext λ _ _ → refl
□-comult-≅ HX .inverses .invr = ext λ _ _ → refl

□-⊆ : X ⊆ X' → □⟨ X ⟩ => □⟨ X' ⟩
□-⊆ H⊆ .η A .fst x     = x
□-⊆ H⊆ .η A .snd g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → inr H⋆
  (inl Hg) → inl $ flip □-map Hg λ (W , HW , H≤ , h , g' , p) →
    W , H⊆ _ HW , H≤ , h , g' , p
□-⊆ H⊆ .is-natural _ _ _ = ext λ _ → refl

□-top : □⟨ X ⟩₀ top ≅ top
□-top .to             = !
□-top .from .fst      = _
□-top .from .snd _ _  = inr (inc (_ , refl))
□-top .inverses .invl = ext λ _ → refl
□-top .inverses .invr = ext λ _ → refl

□-prod : ∀ {A B} → Hom (□⟨ X ⟩₀ (A ⊗₀ B)) (□⟨ X ⟩₀ A ⊗₀ □⟨ X ⟩₀ B)
□-prod .fst x     = x
□-prod .snd g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → case H⋆ of λ x y p →
    inr (inc (_ , ap (fst ⊙_) p)) , inr (inc (_ , ap (snd ⊙_) p))
  (inl Hg) → flip (□-elim (λ _ → hlevel 1)) Hg λ (W , HW , H≤ , h , (g' , Hg') , p) →
      inl (inc (W , HW , H≤ , h , (fst ⊙ g' , Hg' .fst) , ap (fst ⊙_) p))
    , inl (inc (W , HW , H≤ , h , (snd ⊙ g' , Hg' .snd) , ap (snd ⊙_) p))

□-prod'
  : is-meet-closed X → ∀ {A B} → Hom (□⟨ X ⟩₀ A ⊗₀ □⟨ X ⟩₀ B) (□⟨ X ⟩₀ (A ⊗₀ B))
□-prod' HX .fst x = x
□-prod' {X} HX {A} {B} .snd g (Hg₀ , Hg₀') = case Hg₀ of λ where
  (inr H⋆) → case H⋆ of λ x p → case Hg₀' of λ where
    (inr H⋆') → case H⋆' of λ y q → inr (inc (_ , ap₂ ⟨_,_⟩ p q))
    (inl Hg') → inl $ flip □-map Hg' λ (W , HW , H≤ , h , (f , Hf) , q) →
      W , HW , H≤ , h , (_ , A .snd .pt-sec x , Hf) , ap₂ ⟨_,_⟩ p q
  (inl Hg) → flip (□-elim (λ _ → hlevel 1)) Hg λ (W , HW , H≤ , h , (f , Hf) , p) →
    case Hg₀' of λ where
      (inr H⋆') → case H⋆' of λ x q →
        inl (inc (W , HW , H≤ , h , (_ , Hf , B .snd .pt-sec x) , ap₂ ⟨_,_⟩ p q))
      (inl Hg') →
        flip (□-elim (λ _ → hlevel 1)) Hg' λ (W' , HW' , H≤' , h' , (f' , Hf') , q) →
        case HX (_ , HW) (_ , HW') of λ where
          (inl W-incompat)   → absurd (W-incompat _ H≤ H≤')
          (inr (glb , Hglb)) →
            let fac = inc
                  ( (W .fst + W' .fst , Meet.glb glb)
                  , Hglb
                  , Meet.greatest glb _ H≤ H≤'
                  , (uncurry _++_ ⊙ ⟨ h .fst , h' .fst ⟩ , tup-reg (h .snd) (h' .snd))
                  , ( ×-map f f' ⊙ split {m = W .fst}
                    , A .snd .is-sec-∘ _ (_ , inl (Meet.meet≤l glb , proj-reg₁)) Hf
                    , B .snd .is-sec-∘ _ (_ , inl (Meet.meet≤r glb , proj-reg₂)) Hf'
                    )
                  , ap₂ ⟨_,_⟩ p q
                  ∙ ap (λ z → ×-map f f' ⊙ z ⊙ ⟨ h .fst , h' .fst ⟩)
                       (sym $ funext (Equiv.ε (vec-sum-prod (W .fst))))
                  )
            in
            inl fac

□-prod-≅
  : is-meet-closed X → ∀ {A B} → □⟨ X ⟩₀ (A ⊗₀ B) ≅ (□⟨ X ⟩₀ A ⊗₀ □⟨ X ⟩₀ B)
□-prod-≅ HX .to             = □-prod
□-prod-≅ HX .from           = □-prod' HX
□-prod-≅ HX .inverses .invl = ext λ _ _ → refl
□-prod-≅ HX .inverses .invr = ext λ _ _ → refl

□⟨⊤⟩-Id : Id => □⟨ Reg⊆-lat.top ⟩
□⟨⊤⟩-Id .η A .fst x        = x
□⟨⊤⟩-Id .η A .snd {U} g Hg =
  inl (inc (U , tt , ≤-refl , ((λ x → x) , id-reg) , (g , Hg) , refl))
□⟨⊤⟩-Id .is-natural _ _ _  = ext λ _ → refl

𝔇ℝ[_] : Reg↓ → 𝔇.Ob
𝔇ℝ[ c ] .fst = el! ℝ
𝔇ℝ[ c ] .snd = cpsh where
  cpsh : CPSh-on _
  cpsh .is-sec U f .∣_∣ =
    (U .snd ∈ c .hom × f' ∈ ⟨ U .snd ⟩-reg) ∗ (f' ∈ is-const)
    where f' = make {n = 1} ⊙ f
  cpsh .is-sec U f .is-tr = hlevel 1
  cpsh .is-sec-∘ g h Hg = case h .snd of λ where
    (inr H⋆)        → case H⋆ of λ _ p → inr (inc (_ , ap ((make ⊙ g) ⊙_) p))
    (inl (H≤ , Hh)) → case Hg of λ where
      (inr H⋆)         → case H⋆ of λ _ p → inr (inc (_ , ap (_⊙ h .fst) p))
      (inl (HU , Hg')) → inl (c .pres-≤ H≤ HU , ∘-reg (⊆-reg H≤ _ Hg') Hh)
  cpsh .pt-sec x = inr (inc (make x , refl))

□-𝔇ℝ : □⟨ X ⟩₀ 𝔇ℝ[ c ] ≅ 𝔇ℝ[ Close-downward · (X ∩ c .hom) ]
□-𝔇ℝ .to .fst x = x
□-𝔇ℝ {c = c} .to .snd {U} g Hg₀ = case Hg₀ of λ where
  (inr H⋆) → case H⋆ of λ x p → inr (inc (_ , ap (make ⊙_) p))
  (inl Hg) →
    flip (□-elim (λ _ → hlevel 1)) Hg λ (W , HW , H≤ , h , (g' , Hg₀') , p) →
    case Hg₀' of λ where
      (inr H⋆)  → case H⋆ of λ x q →
        inr (inc (_ , ap (make {n = 1} ⊙_) p ∙ ap (_⊙ h .fst) q))
      (inl (Hc , Hreg)) → inl
        ( inc (W .snd , H≤ , HW , Hc)
        , subst (λ f → ∣ ⟨ U .snd ⟩-reg f ∣)
          (ap (make ⊙_) (sym p)) (∘-reg (⊆-reg H≤ _ Hreg) (h .snd))
        )
□-𝔇ℝ .from .fst x = x
□-𝔇ℝ {X} {c} .from .snd {U} g Hg = case Hg of λ where
  (inr H⋆) → case H⋆ of λ x p → inr (inc (_ , ext λ z → p $ₚ z $ₚ fzero))
  (inl (HU , Hreg)) → inl $ flip □-map HU λ (z , U≤z , Hz , Hz') →
    ( (1 , z)
    , Hz
    , U≤z
    , (make ⊙ g , Hreg)
    , ( (λ r → r fzero)
      , inl
        ( Hz'
        , subst (λ f → ∣ ⟨ z ⟩-reg f ∣) (ext λ x → Fin-cases refl λ ()) id-reg
        )
      )
    , refl
    )
□-𝔇ℝ .inverses .invl = ext λ _ → refl
□-𝔇ℝ .inverses .invr = ext λ _ → refl

𝔇ℝ-≤ : c ⊆ c' → Hom 𝔇ℝ[ c ] 𝔇ℝ[ c' ]
𝔇ℝ-≤ H≤ .fst x = x
𝔇ℝ-≤ H≤ .snd g Hg = case Hg of λ where
  (inl Hreg) → inl (H≤ _ (Hreg .fst) , Hreg .snd)
  (inr H⋆) → inr H⋆

𝔇ℝ-const : ℝ → Hom top 𝔇ℝ[ c ]
𝔇ℝ-const r .fst _       = r
𝔇ℝ-const {c} r .snd _ _ = 𝔇ℝ[ c ] .snd .pt-sec r

𝔇ℝ'[_] : Reg↓ ^ n → 𝔇.Ob
𝔇ℝ'[ cs ] = 𝔇-ip.ΠF λ i → 𝔇ℝ[ cs i ]
