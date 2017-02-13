{-# OPTIONS --without-K #-}

module Term where

open import Lib
open import Type

-- Term syntax
--------------------------------------------------------------------------------

data Con : Con' → Set where
  ∙    : Con ∙
  _,_  : ∀ {Γ'} → Con Γ' → Ty Γ' → Con Γ'
  _,*  : ∀ {Γ'} → Con Γ' → Con (Γ' ,*)

infix 3 _∈_
data _∈_ : ∀ {Δ} (A : Ty Δ) → Con Δ → Set where
  vz  : ∀ {Δ}{A : Ty Δ}{Γ}   → A ∈ (Γ , A)
  vs  : ∀ {Δ}{A : Ty Δ}{B Γ} → A ∈ Γ → A ∈ (Γ , B)
  vs* : ∀ {Δ}{A : Ty Δ}{Γ}   → A ∈ Γ → Tyₑ wk' A ∈ (Γ ,*)

data Tm {Δ} (Γ : Con Δ) : Ty Δ → Set where
  var  : ∀ {A} → A ∈ Γ → Tm Γ A
  lam  : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app  : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  tlam : ∀ {A} → Tm (Γ ,*) A → Tm Γ (∀' A)
  tapp : ∀ {A} → Tm Γ (∀' A) → (B : Ty Δ) → Tm Γ (Tyₛ (id'ₛ , B) A)

-- Term embedding
--------------------------------------------------------------------------------

data OPE : ∀ {Γ Δ} → OPE' Γ Δ → Con Γ → Con Δ → Set where
  ∙     : OPE ∙ ∙ ∙
  drop' : ∀ {Γ Δ σ δ ν}   → OPE {Γ}{Δ} σ δ ν → OPE (drop σ) (δ ,*)         ν
  keep' : ∀ {Γ Δ σ δ ν}   → OPE {Γ}{Δ} σ δ ν → OPE (keep σ) (δ ,*)         (ν ,*)
  drop  : ∀ {Γ Δ σ δ ν A} → OPE {Γ}{Δ} σ δ ν → OPE σ        (δ , A)        ν
  keep  : ∀ {Γ Δ σ δ ν A} → OPE {Γ}{Δ} σ δ ν → OPE σ        (δ , Tyₑ σ A) (ν , A)

OPE'-of : ∀ {Γ' Δ' σ' Γ Δ} → OPE {Γ'}{Δ'} σ' Γ Δ → OPE' Γ' Δ'
OPE'-of {σ' = σ'} _ = σ'

Con'-of : ∀ {Γ} → Con Γ → Con'
Con'-of {Γ} _ = Γ

keepₜ : ∀ {Γ Δ σ δ ν A} → OPE {Γ}{Δ} σ δ ν → OPE σ (δ , Tyₑ σ A) (ν , A)
keepₜ = keep

idₑ : ∀ {Γ'}{Γ : Con Γ'} → OPE id'ₑ Γ Γ
idₑ {∙}     {∙}     = ∙
idₑ {∙}     {Γ , A} =
  coe ((λ x → OPE ∙ (Γ , x) (Γ , A)) & Ty-idₑ A) (keepₜ idₑ)
idₑ {Γ' ,*} {Γ , A} =
  coe ((λ x → OPE id'ₑ (Γ , x) (Γ , A)) & Ty-idₑ A) (keepₜ idₑ)
idₑ {Γ' ,*} {Γ ,*}  = keep' (idₑ {Γ'}{Γ})

∈ₑ : ∀ {Γ' Δ'}{σ' : OPE' Γ' Δ'}{Γ Δ A} →  OPE σ' Γ Δ → A ∈ Δ → Tyₑ σ' A ∈ Γ
∈ₑ ∙         ()
∈ₑ {A = A} (drop' {σ = σ} {δ} σ') v =
  coe
    ((_∈ (δ ,*)) & (Ty-∘ₑ σ wk' A ◾ (λ x → Tyₑ (drop x) A) & idr'ₑ σ))
  (vs* (∈ₑ σ' v))
∈ₑ (keep' {σ = σ} {δ} σ') (vs* {A = A} v) =
  coe
    ((_∈ (δ ,*)) & (Ty-∘ₑ σ wk' A
       ◾ (λ x → Tyₑ (drop x) A) & (idr'ₑ σ ◾ idl'ₑ σ ⁻¹) ◾ Ty-∘ₑ wk' (keep σ) A ⁻¹))
  (vs* (∈ₑ σ' v))
∈ₑ (drop σ)  v      = vs (∈ₑ σ v)
∈ₑ (keep σ) vz      = vz
∈ₑ (keep σ) (vs v)  = vs (∈ₑ σ v)

Tmₑ : ∀ {Γ' Δ'}{σ' : OPE' Γ' Δ'}{Γ Δ A} → OPE σ' Γ Δ → Tm Δ A → Tm Γ (Tyₑ σ' A)
Tmₑ σ (var v)    = var (∈ₑ σ v)
Tmₑ σ (lam t)    = lam (Tmₑ (keep σ) t)
Tmₑ σ (app f x)  = app (Tmₑ σ f) (Tmₑ σ x)
Tmₑ σ (tlam t)   = tlam (Tmₑ (keep' σ) t)
Tmₑ {σ' = σ'}{Γ} σ (tapp {A} t B) =
  coe (Tm Γ &
      (Ty-ₑ∘ₛ (keep σ') (id'ₛ , Tyₑ σ' B) A
    ◾ (λ x → Tyₛ (x , Tyₑ σ' B) A) &
        (idr'ₑₛ σ' ◾ idl'ₛₑ σ' ⁻¹) ◾ Ty-ₛ∘ₑ (id'ₛ , B) σ' A ⁻¹ ))
  (tapp (Tmₑ σ t) (Tyₑ σ' B))

_∘ₑ_ :
  ∀ {Γ' Δ' Σ' σ' δ' Γ Δ Σ} → OPE {Δ'}{Σ'} σ' Δ Σ → OPE {Γ'}{Δ'} δ' Γ Δ
  → OPE (σ' ∘'ₑ δ') Γ Σ
σ       ∘ₑ ∙       = σ
σ       ∘ₑ drop' δ = drop' (σ ∘ₑ δ)
σ       ∘ₑ drop  δ = drop  (σ ∘ₑ δ)
drop' σ ∘ₑ keep' δ = drop' (σ ∘ₑ δ)
keep' σ ∘ₑ keep' δ = keep' (σ ∘ₑ δ)
drop  σ ∘ₑ keep  δ = drop  (σ ∘ₑ δ)
_∘ₑ_ {σ' = σ'} {δ'} (keep {ν = ν} {A} σ) (keep {δ = δ₁} δ₂) =
  coe ((λ x → OPE (σ' ∘'ₑ δ') (δ₁ , x) (ν , A)) & (Ty-∘ₑ σ' δ' A ⁻¹))
  (keepₜ {A = A} (σ ∘ₑ δ₂))


-- Normal forms
--------------------------------------------------------------------------------

mutual
  data Nf {Γ} (Δ : Con Γ) : Ty Γ → Set where
    lam  : ∀ {A B} → Nf (Δ , A) B → Nf Δ (A ⇒ B)
    tlam : ∀ {A} → Nf (Δ ,*) A → Nf Δ (∀' A)
    ne   : ∀ {v} → Ne Δ (var v) → Nf Δ (var v)

  data Ne {Γ}(Δ : Con Γ) : Ty Γ → Set where
    var  : ∀ {A} → A ∈ Δ → Ne Δ A
    app  : ∀ {A B} → Ne Δ (A ⇒ B) → Nf Δ A → Ne Δ B
    tapp : ∀ {A} → Ne Δ (∀' A) → (B : Ty Γ) → Ne Δ (Tyₛ (id'ₛ , B) A)

tappₙₑ : ∀ {Γ}{Δ : Con Γ}{A} → Ne Δ (∀' A) → (B : Ty Γ) → Ne Δ (Tyₛ (id'ₛ , B) A)
tappₙₑ = tapp

mutual
  Nfₑ : ∀ {Γ' Γ Δ' Δ σ' A} → OPE {Γ'}{Δ'} σ' Γ Δ → Nf Δ A → Nf Γ (Tyₑ σ' A)
  Nfₑ σ (lam t)  = lam (Nfₑ (keep σ) t)
  Nfₑ σ (tlam t) = tlam (Nfₑ (keep' σ) t)
  Nfₑ σ (ne n)   = ne (Neₑ σ n)

  Neₑ : ∀ {Γ' Γ Δ' Δ A σ'} → OPE {Γ'}{Δ'} σ' Γ Δ → Ne Δ A → Ne Γ (Tyₑ σ' A)
  Neₑ σ (var v)    = var (∈ₑ σ v)
  Neₑ σ (app n t)  = app (Neₑ σ n) (Nfₑ σ t)
  Neₑ {Γ = Γ}{σ' = σ'} σ (tapp {A} n B) =
    coe (Ne Γ &
         (Ty-ₑ∘ₛ (keep σ') (id'ₛ , Tyₑ σ' B) A
       ◾ (λ x → Tyₛ (x , Tyₑ σ' B) A) & (idr'ₑₛ σ' ◾ idl'ₛₑ σ' ⁻¹)
       ◾ Ty-ₛ∘ₑ (id'ₛ , B) σ' A ⁻¹))
    (tappₙₑ (Neₑ σ n) (Tyₑ (OPE'-of σ) B))

-- Term substitution
---------------------------------------------------------------------------------

