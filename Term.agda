{-# OPTIONS --without-K --type-in-type --rewriting #-}

module Term where

open import Lib
open import Type

-- Term syntax
--------------------------------------------------------------------------------

data Con : Con' → Set where
  ∙    : Con ∙
  _,_  : ∀ {Δ} → Con Δ → Ty Δ → Con Δ
  _,*  : ∀ {Δ} → Con Δ → Con (Δ ,*)

postulate
  coe-Con-, :
    ∀ (Δ : I → Con') σ A
    → coe (⟨ i ⟩ Con (Δ i)) (σ , A) ↦ coe (⟨ i ⟩ Con (Δ i)) σ  , coe (⟨ i ⟩ Ty (Δ i)) A
  coe-Con-,* :
    ∀ (Δ : I → Con') σ
    → coe (⟨ i ⟩ Con (Δ i ,*)) (σ ,*) ↦ coe (⟨ i ⟩ Con (Δ i)) σ  ,*

{-# REWRITE coe-Con-,  #-}
{-# REWRITE coe-Con-,* #-}

infix 3 _∈_
data _∈_ : ∀ {Δ} (A : Ty Δ) → Con Δ → Set where
  vz  : ∀ {Δ}{A : Ty Δ}{Γ}   → A ∈ (Γ , A)
  vs  : ∀ {Δ}{A : Ty Δ}{B Γ} → A ∈ Γ → A ∈ (Γ , B)
  vs* : ∀ {Δ}{A : Ty Δ}{Γ}   → A ∈ Γ → Tyₑ wk' A ∈ (Γ ,*)

postulate
  coe-∈-vz :
    ∀ (Δ : I → Con')(A : ∀ i → Ty (Δ i))(Γ : ∀ i → Con (Δ i))
    → coe (⟨ i ⟩ (A i ∈ (Γ i , A i))) vz ↦ vz
  coe-∈-vs :
    ∀ (Δ : I → Con')(A B : ∀ i → Ty (Δ i))(Γ : ∀ i → Con (Δ i)) (v : A ₀ ∈ Γ ₀)
    → coe (⟨ i ⟩ (A i ∈ (Γ i , B i))) (vs v) ↦ vs (coe (⟨ i ⟩ (A i ∈ Γ i)) v)
  coe-∈-vs* :
    ∀ (Δ : I → Con')(A : ∀ i → Ty (Δ i))(Γ : ∀ i → Con (Δ i)) (v : A ₀ ∈ Γ ₀)
    → coe (⟨ i ⟩ (Tyₑ wk' (A i) ∈ (Γ i ,*))) (vs* v) ↦ vs* (coe (⟨ i ⟩ (A i ∈ Γ i)) v)

{-# REWRITE coe-∈-vz  #-}
{-# REWRITE coe-∈-vs  #-}
{-# REWRITE coe-∈-vs* #-}

data Tm {Δ} (Γ : Con Δ) : Ty Δ → Set where
  var  : ∀ {A} → A ∈ Γ → Tm Γ A
  lam  : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app  : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  tlam : ∀ {A} → Tm (Γ ,*) A → Tm Γ (∀' A)
  tapp : ∀ {A} → Tm Γ (∀' A) → (B : Ty Δ) → Tm Γ (Tyₛ (id'ₛ , B) A)

postulate
  coe-Tm-var :
    ∀ (Γ' : I → Con')(Γ : ∀ i → Con (Γ' i))(A : ∀ i → Ty (Γ' i)) v
    → coe (⟨ i ⟩ Tm (Γ i) (A i)) (var v) ↦ var (coe (⟨ i ⟩ (A i ∈ Γ i)) v)
  coe-Tm-lam :
    ∀ (Γ' : I → Con')(Γ : ∀ i → Con (Γ' i))(A B  : ∀ i → Ty (Γ' i)) t
    → coe (⟨ i ⟩ Tm (Γ i) (A i ⇒ B i)) (lam t) ↦ lam (coe (⟨ i ⟩ Tm (Γ i , A i) (B i)) t)
  coe-Tm-app :
    ∀ (Γ' : I → Con')(Γ : ∀ i → Con (Γ' i)) (A : Ty (Γ' ₀))(B : ∀ i → Ty (Γ' i)) (f : Tm (Γ ₀) (A ⇒ B ₀)) x
    → coe (⟨ i ⟩ Tm (Γ i) (B i)) (app f x)
    ↦ app
        (coe (⟨ i ⟩ Tm (Γ i) (coe (⟨ j ⟩ Ty (Γ' (j [ ₀ - i ]))) A ⇒ B i)) f)
        (coe (⟨ i ⟩ Tm (Γ i) (coe (⟨ j ⟩ Ty (Γ' (j [ ₀ - i ]))) A)) x)
  coe-Tm-tlam :
    ∀ (Γ' : I → Con')(Γ : ∀ i → Con (Γ' i))(A : ∀ i → Ty (Γ' i ,*)) t
    → coe (⟨ i ⟩ Tm (Γ i) (∀' (A i))) (tlam t) ↦ tlam (coe (⟨ i ⟩ Tm (Γ i ,*) (A i)) t)
  coe-Tm-tapp :
    ∀ (Γ' : I → Con')(Γ : ∀ i → Con (Γ' i)) (B : ∀ i → Ty (Γ' i))(A : ∀ i → Ty (Γ' i ,*)) t
    → coe (⟨ i ⟩ Tm (Γ i) (Tyₛ (id'ₛ , B i) (A i))) (tapp {Γ' ₀}{Γ ₀}{A ₀} t (B ₀))
    ↦ tapp {Γ' ₁}{Γ ₁}{A ₁} (coe (⟨ i ⟩ Tm (Γ i) (∀' (A i))) t) (B ₁)

{-# REWRITE coe-Tm-var  #-}
{-# REWRITE coe-Tm-lam  #-}
{-# REWRITE coe-Tm-app  #-}
{-# REWRITE coe-Tm-tlam #-}
{-# REWRITE coe-Tm-tapp #-}

-- Term embedding
--------------------------------------------------------------------------------

data OPE : ∀ {Γ Δ} → OPE' Γ Δ → Con Γ → Con Δ → Set where
  ∙     : OPE ∙ ∙ ∙
  drop' : ∀ {Γ Δ σ δ ν}   → OPE {Γ}{Δ} σ δ ν → OPE (drop σ) (δ ,*)         ν
  keep' : ∀ {Γ Δ σ δ ν}   → OPE {Γ}{Δ} σ δ ν → OPE (keep σ) (δ ,*)         (ν ,*)
  drop  : ∀ {Γ Δ σ δ ν A} → OPE {Γ}{Δ} σ δ ν → OPE σ        (δ , A)        ν
  keep  : ∀ {Γ Δ σ δ ν A} → OPE {Γ}{Δ} σ δ ν → OPE σ        (δ , Tyₑ σ A) (ν , A)

-- postulate
--   coe-OPE-drop' :
--   ∀ (Γ' : I → Con')(Δ'


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


-- options for proving things
-- 1. define and apply assloads of coe reduction rules (most tedious)
-- 2. define OTT-like structure for coercions (dunno how well it works)
-- 3. use proof automation, maybe throw in JMeq too (dunno how performant, how well it works
--                                                   in Agda)


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

