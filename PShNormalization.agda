
{-# OPTIONS --without-K --type-in-type #-}

-- Normalization with a presheaf logical predicate model for types and simple presheaf model for terms.
-- We want to only have the minimum necessary structure for normalization, so that external correctness
-- proofs don't have to deal with mountains of coercion. We have more than enough coercion in any case.

module PShNormalization where

open import Lib
open import Type
open import Term

record Cand {Γ'} Γ A : Set where
  constructor con
  field
    S : Set
    Q : S → Nf {Γ'} Γ A
    U : Ne Γ A → S
open Cand

-- todo: action on morphism : (δ' : OPE' Σ' Δ') → Aᴹ {Γ'} Δ' Δ σ' → Aᴹ {Γ'} Σ' Σ (δ' ∘'ₑ σ')
--       + maybe action on id and ∘

*ᴹ : ∀ {Γ'} → Ty Γ' → Set
*ᴹ {Γ'} A = ∀ Δ' Δ σ' → Cand {Δ'} Δ (Tyₑ σ' A)

*ᴹₑ : ∀ {Γ' Δ' A}(σ' : OPE' Δ' Γ') → *ᴹ {Γ'} A → *ᴹ {Δ'} (Tyₑ σ' A)
*ᴹₑ {Γ'}{Δ'}{A} σ' f Σ' Σ δ' = coe (Cand Σ & (Ty-∘ₑ σ' δ' A ⁻¹)) (f Σ' Σ (σ' ∘'ₑ δ'))

*ᴹ-idₑ : ∀ {Γ' A} (Aᴹ : *ᴹ {Γ'} A) → *ᴹₑ id'ₑ Aᴹ ≅ Aᴹ
*ᴹ-idₑ {A = A} Aᴹ = ext̃ λ Σ' → ext̃ λ Σ → ext̃ λ σ' →
    uncoe (Cand Σ & (Ty-∘ₑ id'ₑ σ' A ⁻¹)) _
  ◾̃ ap̃ (Aᴹ Σ' Σ) (idl'ₑ σ')

*ᴹ-∘ₑ :
  ∀ {Γ' Δ' Σ'}{A : Ty Γ'} (σ' : OPE' Δ' Γ') (δ' : OPE' Σ' Δ') (Aᴹ : *ᴹ {Γ'} A)
  → *ᴹₑ (σ' ∘'ₑ δ') Aᴹ ≅ *ᴹₑ δ' (*ᴹₑ σ' Aᴹ)
*ᴹ-∘ₑ {A = A} σ' δ' Aᴹ = ext̃ λ Σ' → ext̃ λ Σ → ext̃ λ ν' →
    uncoe (Cand Σ & (Ty-∘ₑ (σ' ∘'ₑ δ') ν' A ⁻¹)) _
  ◾̃ ap̃ (Aᴹ Σ' Σ) (ass'ₑ σ' δ' ν')
  ◾̃ uncoe (Cand Σ & (Ty-∘ₑ σ' (δ' ∘'ₑ ν') A ⁻¹)) _ ⁻¹̃
  ◾̃ uncoe (Cand Σ & (Ty-∘ₑ δ' ν' (Tyₑ σ' A) ⁻¹)) _ ⁻¹̃

--------------------------------------------------------------------------------

data Con'ᴹ : (Γ' : Con') → ∀ {Δ'} → Sub' Δ' Γ' → Set where
  ∙   : ∀ {Δ'} → Con'ᴹ ∙ {Δ'} ∙
  _,_ : ∀ {Γ' Δ' σ' A} → Con'ᴹ Γ' {Δ'} σ' → *ᴹ A → Con'ᴹ (Γ' ,*) (σ' , A)

Con'ᴹ, : ∀ {Γ' Δ' σ' A} → Con'ᴹ Γ' {Δ'} σ' → *ᴹ A → Con'ᴹ (Γ' ,*) (σ' , A)
Con'ᴹ, = _,_

Con'ᴹₑ : ∀ {Γ' Δ' σ' Σ'} δ' → Con'ᴹ Γ' {Δ'} σ' → Con'ᴹ Γ' {Σ'} (σ' ₛ∘'ₑ δ')
Con'ᴹₑ δ' ∙          = ∙
Con'ᴹₑ δ' (σ'ᴹ , Aᴹ) = Con'ᴹₑ δ' σ'ᴹ , *ᴹₑ δ' Aᴹ

u* : ∀ {Γ'}(v : *∈ Γ') → *ᴹ {Γ'} (var v)
u* {Γ'} v Δ' Δ σ' = con (Ne Δ (var (*∈ₑ σ' v))) ne (λ n → n)

*∈ᴹ : ∀ {Γ'}(v : *∈ Γ') → ∀ {Δ'} Δ (σ : Sub' Δ' Γ')(σᴹ : Con'ᴹ Γ' σ) → Cand Δ (*∈ₛ σ v)
*∈ᴹ vz     Δ (σ , A) (σᴹ , Aᴹ) = coe (Cand Δ & Ty-idₑ A) (Aᴹ _ Δ id'ₑ)
*∈ᴹ (vs v) Δ (σ , _) (σᴹ , _) = *∈ᴹ v Δ σ σᴹ

Tyᴹ : ∀ {Γ'}(A : Ty Γ') → ∀ {Δ'} Δ (σ' : Sub' Δ' Γ')(σ'ᴹ : Con'ᴹ Γ' σ') → Cand Δ (Tyₛ σ' A)
Tyᴹ (var v) σ' σ'ᴹ = *∈ᴹ v σ' σ'ᴹ

Tyᴹ {Γ'} (A ⇒ B) {Δ'} Δ σ' σ'ᴹ = con

  (∀ {Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ) → Tyᴹ A Σ _ (Con'ᴹₑ δ' σ'ᴹ) .S → Tyᴹ B Σ _ (Con'ᴹₑ δ' σ'ᴹ) .S)

  (λ fᴹ → lam
    (coe ((λ x → Nf (Δ , Tyₛ x A) (Tyₛ x B)) & idr'ₛₑ σ')
      (Tyᴹ B _ _ (Con'ᴹₑ id'ₑ σ'ᴹ) .Q
      (fᴹ (drop idₑ) (Tyᴹ A _ _ (Con'ᴹₑ id'ₑ σ'ᴹ) .U (var vz))))))

  (λ n {Σ'}{Σ}{δ'} δ aᴹ → let σ'ᴹ' = Con'ᴹₑ δ' σ'ᴹ in
    Tyᴹ B _ _ σ'ᴹ' .U (app (coe (Ne Σ & Ty-ₛ∘ₑ σ' δ' (A ⇒ B)) (Neₑ δ n)) (Tyᴹ A _ _ σ'ᴹ' .Q aᴹ)))

Tyᴹ {Γ'} (∀' A) {Δ'} Δ σ' σ'ᴹ = con
  (∀ {Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ) (B : Ty Σ')(Bᴹ : *ᴹ B) → Tyᴹ A Σ _ (Con'ᴹₑ δ' σ'ᴹ , Bᴹ) .S)

  (λ fᴹ →
    tlam (Tyᴹ A _ _ (Con'ᴹₑ (drop id'ₑ) σ'ᴹ , u* vz) .Q (fᴹ (drop' idₑ) _ (u* vz))))

  (λ n {Σ'}{Σ}{δ'} δ B Bᴹ →
    Tyᴹ A _ _ (Con'ᴹₑ δ' σ'ᴹ , Bᴹ) .U
      (coe
          (Ne Σ & (Ty-ₑ∘ₛ (keep δ') (id'ₛ , B) (Tyₛ (keep'ₛ σ') A)
        ◾ Ty-∘ₛ (keep'ₛ σ') ((δ' ₑ∘'ₛ id'ₛ) , B) A
        ◾ (λ x → Tyₛ (x , B) A) &
            (ass'ₛₑₛ σ' (drop id'ₑ) ((δ' ₑ∘'ₛ id'ₛ) , B)
           ◾ ((λ x → σ' ∘'ₛ id'ₑ ₑ∘'ₛ x) & idr'ₑₛ δ')
           ◾ (σ' ∘'ₛ_) & idl'ₑₛ (emb'ₑ δ')
           ◾ emb'-∘ₛ σ' δ')))
      (tappₙₑ (Neₑ δ n) B)))

--------------------------------------------------------------------------------

Con'ᴹ-idₑ : ∀ {Γ' Δ' σ'}(σ'ᴹ : Con'ᴹ Γ' {Δ'} σ') → Con'ᴹₑ id'ₑ σ'ᴹ ≅ σ'ᴹ
Con'ᴹ-idₑ ∙          = refl̃
Con'ᴹ-idₑ {Δ' = Δ'} (_,_ {Γ'} {σ' = σ'} {A} σ'ᴹ Aᴹ) =
  ap4̃ (λ σ' A σ'ᴹ Aᴹ → Con'ᴹ, {σ' = σ'}{A = A} σ'ᴹ Aᴹ)
    (idr'ₛₑ σ')
    (Ty-idₑ A ~)
    (Con'ᴹ-idₑ σ'ᴹ)
    (*ᴹ-idₑ Aᴹ)

Con'ᴹ-∘ₑ :
  ∀ {Γ' Δ' Σ' Ξ' σ'} δ' (ν' : OPE' Ξ' Σ') σ'ᴹ
  → Con'ᴹₑ {Γ'}{Δ'}{σ'}{Ξ'} (δ' ∘'ₑ ν') σ'ᴹ ≅ Con'ᴹₑ ν' (Con'ᴹₑ δ' σ'ᴹ)
Con'ᴹ-∘ₑ δ' ν' ∙  = refl̃
Con'ᴹ-∘ₑ δ' ν' (_,_ {Γ'} {σ' = σ'} {A} σ'ᴹ Aᴹ) =
  ap4̃ (λ σ' A σ'ᴹ Aᴹ → Con'ᴹ, {σ' = σ'}{A = A} σ'ᴹ Aᴹ)
    (ass'ₛₑₑ σ' δ' ν' ⁻¹)
    (Ty-∘ₑ δ' ν' A ⁻¹ ~)
    (Con'ᴹ-∘ₑ δ' ν' σ'ᴹ)
    (*ᴹ-∘ₑ δ' ν' Aᴹ)

OPE'ᴹ : ∀ {Γ' Δ'}(σ' : OPE' Γ' Δ') → ∀ {Σ' δ'} → Con'ᴹ Γ' {Σ'} δ' → Con'ᴹ Δ' {Σ'} (σ' ₑ∘'ₛ δ')
OPE'ᴹ ∙         {Σ'}  δ'ᴹ       = δ'ᴹ
OPE'ᴹ (drop σ') {Σ'} (δ'ᴹ , _)  = OPE'ᴹ σ' δ'ᴹ
OPE'ᴹ (keep σ') {Σ'} (δ'ᴹ , Aᴹ) = OPE'ᴹ σ' δ'ᴹ , Aᴹ

OPE'ᴹ-idₑ : ∀ {Γ' Δ' σ'}(σ'ᴹ : Con'ᴹ Γ' {Δ'} σ') → OPE'ᴹ id'ₑ σ'ᴹ ≅ σ'ᴹ
OPE'ᴹ-idₑ ∙          = refl̃
OPE'ᴹ-idₑ (_,_ {Γ'} {σ' = σ'} σ'ᴹ Aᴹ) =
  ap2̃ (λ σ' σ'ᴹ → Con'ᴹ, {σ' = σ'} σ'ᴹ Aᴹ) (idl'ₑₛ σ') (OPE'ᴹ-idₑ σ'ᴹ)

OPE'ᴹ-nat :
  ∀ {Γ' Δ' Σ' Ξ' σ'} (δ' : OPE' Δ' Γ') (ν' : OPE' Ξ' Σ') (σ'ᴹ : Con'ᴹ Δ' σ')
  → OPE'ᴹ δ' (Con'ᴹₑ ν' σ'ᴹ) ≅ Con'ᴹₑ ν' (OPE'ᴹ δ' σ'ᴹ)
OPE'ᴹ-nat ∙         ν' σ'ᴹ        = refl̃
OPE'ᴹ-nat (drop δ') ν' (σ'ᴹ , _)  = OPE'ᴹ-nat δ' ν' σ'ᴹ
OPE'ᴹ-nat (keep δ') ν' (σ'ᴹ , Aᴹ) =
  ap2̃ (λ σ' σ'ᴹ → Con'ᴹ, {σ' = σ'} σ'ᴹ (*ᴹₑ ν' Aᴹ))
      (ass'ₑₛₑ δ' _ ν' ⁻¹) (OPE'ᴹ-nat δ' ν' σ'ᴹ)

--------------------------------------------------------------------------------

*∈ᴹₑ :
  ∀ {Γ' v Δ' Δ σ' σ'ᴹ Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ)
  → *∈ᴹ {Γ'} v Δ σ' σ'ᴹ .S → *∈ᴹ v Σ _ (Con'ᴹₑ δ' σ'ᴹ) .S
*∈ᴹₑ {v = vz {Γ'}}{Δ'}{Δ}{σ' , A}{σ'ᴹ , x} {Σ'} {Σ} {δ'} δ aᴹ = {!!} -- *ᴹ A functor
*∈ᴹₑ {v = vs v}{σ'ᴹ = σ'ᴹ , x} δ aᴹ = *∈ᴹₑ{v = v}{σ'ᴹ = σ'ᴹ} δ aᴹ

Tyᴹₑ :
  ∀ {Γ' A Δ' Δ σ' σ'ᴹ Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ)
  → Tyᴹ {Γ'} A Δ σ' σ'ᴹ .S → Tyᴹ A Σ _ (Con'ᴹₑ δ' σ'ᴹ) .S
Tyᴹₑ {A = var v} δ aᴹ = *∈ᴹₑ {v = v} δ aᴹ

Tyᴹₑ {Γ'} {A ⇒ B} {σ' = σ'} {σ'ᴹ} {δ' = δ'} δ tᴹ {Σ'} {Σ} {ν'} ν aᴹ =
  coe (ap2 (λ x y → Tyᴹ B Σ x y .S) (ass'ₛₑₑ σ' δ' ν' ⁻¹) (Con'ᴹ-∘ₑ δ' ν' σ'ᴹ))
    (tᴹ (δ ∘ₑ ν)
    (coe (ap2 (λ x y → Tyᴹ A Σ x y .S) (ass'ₛₑₑ σ' δ' ν') (Con'ᴹ-∘ₑ δ' ν' σ'ᴹ ⁻¹̃))
      aᴹ))

Tyᴹₑ {A = ∀' A } {σ' = σ'} {σ'ᴹ} {δ' = δ'} δ tᴹ {Ξ'} {Ξ} {ν'} ν B Bᴹ =
  coe (ap2 (λ x y → Tyᴹ A Ξ x y .S) ((_, B) & (ass'ₛₑₑ σ' δ' ν' ⁻¹))
        (ap2̃ (λ σ' σ'ᴹ → Con'ᴹ, {σ' = σ'} σ'ᴹ Bᴹ)
         (ass'ₛₑₑ σ' δ' ν' ⁻¹) (Con'ᴹ-∘ₑ δ' ν' σ'ᴹ)))
    (tᴹ (δ ∘ₑ ν) B Bᴹ)

--------------------------------------------------------------------------------

*∈ₑᴹ :
  ∀ {Γ'} v {Δ' Σ'} Σ δ' {σ'} σ'ᴹ
  → *∈ᴹ {Δ'} (*∈ₑ {Γ'} δ' v) {Σ'} Σ σ' σ'ᴹ .S ≡ *∈ᴹ v Σ (δ' ₑ∘'ₛ σ') (OPE'ᴹ δ' σ'ᴹ) .S
*∈ₑᴹ v      Σ ∙         σ'ᴹ        = refl
*∈ₑᴹ v      Σ (drop δ') (σ'ᴹ , _ ) = *∈ₑᴹ v Σ δ' σ'ᴹ
*∈ₑᴹ vz     Σ (keep δ') (σ'ᴹ , Aᴹ) = refl
*∈ₑᴹ (vs v) Σ (keep δ') (σ'ᴹ , Aᴹ) = *∈ₑᴹ v Σ δ' σ'ᴹ

Tyₑᴹ :
  ∀ {Γ'} A {Δ' Σ'} Σ δ' {σ'} σ'ᴹ
  → Tyᴹ {Δ'} (Tyₑ {Γ'} δ' A) {Σ'} Σ σ' σ'ᴹ .S ≡ Tyᴹ A Σ (δ' ₑ∘'ₛ σ') (OPE'ᴹ δ' σ'ᴹ) .S
Tyₑᴹ {Γ'} (var v) {Δ'} {Σ'} Σ δ' {σ'} σ'ᴹ = *∈ₑᴹ v Σ δ' σ'ᴹ
Tyₑᴹ {Γ'} (A ⇒ B) {Δ'} {Σ'} Σ δ' {σ'} σ'ᴹ =
  Πi-≡ λ Ξ' → Πi-≡ λ Ξ → Πi-≡ λ ν' → Π-≡ λ ν →
    (λ x y → x → y)
      & (Tyₑᴹ A Ξ δ' (Con'ᴹₑ ν' σ'ᴹ)
        ◾ ap2 (λ x y → Tyᴹ A Ξ x y .S) (ass'ₑₛₑ δ' σ' ν' ⁻¹) (OPE'ᴹ-nat δ' ν' σ'ᴹ))
      ⊗ (Tyₑᴹ B Ξ δ' (Con'ᴹₑ ν' σ'ᴹ)
        ◾ ap2 (λ x y → Tyᴹ B Ξ x y .S) (ass'ₑₛₑ δ' σ' ν' ⁻¹) (OPE'ᴹ-nat δ' ν' σ'ᴹ))
Tyₑᴹ {Γ'} (∀' A)  {Δ'} {Σ'} Σ δ' {σ'} σ'ᴹ =
  Πi-≡ λ Ξ' → Πi-≡ λ Ξ → Πi-≡ λ ν' → Π-≡ λ ν → Π-≡ λ B → Π-≡ λ Bᴹ →
      Tyₑᴹ A Ξ (keep δ') (Con'ᴹₑ ν' σ'ᴹ , Bᴹ)
    ◾ ap2 (λ x y → Tyᴹ A Ξ (x , B) (y , Bᴹ) .S) (ass'ₑₛₑ δ' σ' ν' ⁻¹) (OPE'ᴹ-nat δ' ν' σ'ᴹ)

--------------------------------------------------------------------------------

data Conᴹ : ∀ {Γ'} → Con Γ' → ∀ {Δ'} (Δ : Con Δ'){σ'} → Con'ᴹ Γ' {Δ'} σ' → Set where
  ∙   : ∀ {Δ' Δ} → Conᴹ ∙ {Δ'} Δ ∙
  _,_ : ∀ {Γ' Γ Δ' Δ σ' σ'ᴹ A} → Conᴹ {Γ'} Γ {Δ'} Δ {σ'} σ'ᴹ → Tyᴹ A Δ σ' σ'ᴹ .S → Conᴹ (Γ , A) Δ σ'ᴹ
  _,* : ∀ {Γ' Γ Δ' Δ σ' σ'ᴹ A}{Aᴹ : *ᴹ A} → Conᴹ {Γ'} Γ {Δ'} Δ {σ'} σ'ᴹ → Conᴹ (Γ ,*) Δ (σ'ᴹ , Aᴹ)

Conᴹₑ :
  ∀ {Γ' Γ Δ' Δ σ' σ'ᴹ Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ) → Conᴹ {Γ'} Γ Δ {σ'} σ'ᴹ → Conᴹ Γ Σ (Con'ᴹₑ δ' σ'ᴹ)
Conᴹₑ δ ∙ = ∙
Conᴹₑ δ (_,_ {A = A} Γᴹ tᴹ) = Conᴹₑ δ Γᴹ , Tyᴹₑ {A = A} δ tᴹ
Conᴹₑ δ (Γᴹ ,*) = Conᴹₑ δ Γᴹ ,*

∈ᴹ : ∀ {Γ' Γ A} → _∈_ {Γ'} A Γ → ∀ {Δ' Δ σ'} σ'ᴹ → Conᴹ Γ Δ σ'ᴹ → Tyᴹ {Γ'} A {Δ'} Δ σ' σ'ᴹ .S
∈ᴹ vz       σ'ᴹ      (Γᴹ , t) = t
∈ᴹ (vs v)   σ'ᴹ      (Γᴹ , t) = ∈ᴹ v σ'ᴹ Γᴹ
∈ᴹ (vs* {A = B} v) {Δ = Δ} (_,_ {σ' = σ'} {A} σ'ᴹ x) (Γᴹ ,*) =
  coe (ap2 (λ x₁ y → Tyᴹ B Δ x₁ y .S) (idl'ₑₛ σ' ⁻¹) (OPE'ᴹ-idₑ σ'ᴹ ⁻¹̃)
     ◾ Tyₑᴹ B Δ wk' (σ'ᴹ , x) ⁻¹)
    (∈ᴹ v σ'ᴹ Γᴹ)

Tmᴹ : ∀ {Γ' Γ A} → Tm {Γ'} Γ A → ∀ {Δ' Δ σ'} σ'ᴹ → Conᴹ Γ Δ σ'ᴹ → Tyᴹ {Γ'} A {Δ'} Δ σ' σ'ᴹ .S
Tmᴹ (var v)    σ'ᴹ Γᴹ = ∈ᴹ v σ'ᴹ Γᴹ
Tmᴹ (lam t)    σ'ᴹ Γᴹ = λ δ aᴹ → Tmᴹ t _ (Conᴹₑ δ Γᴹ , aᴹ)

Tmᴹ {A = B} (app {A} f x) {Δ = Δ} {σ'} σ'ᴹ Γᴹ =
  coe (ap2 (λ x₁ y → Tyᴹ B Δ x₁ y .S) (idr'ₛₑ σ') (Con'ᴹ-idₑ σ'ᴹ))
    (Tmᴹ f σ'ᴹ Γᴹ idₑ
      (coe (ap2 (λ x₁ y → Tyᴹ A Δ x₁ y .S) (idr'ₛₑ σ' ⁻¹) (Con'ᴹ-idₑ σ'ᴹ ⁻¹̃))
      (Tmᴹ x σ'ᴹ Γᴹ)))

Tmᴹ (tlam t)   σ'ᴹ Γᴹ = λ δ B Bᴹ → Tmᴹ t (_ , Bᴹ) (Conᴹₑ δ Γᴹ ,*)

Tmᴹ (tapp {A} t B) {Δ = Δ} {σ'} σ'ᴹ Γᴹ =
  coe {!!}  -- Tyₛᴹ
    (Tmᴹ t σ'ᴹ Γᴹ idₑ (Tyₛ σ' B)
    (λ Σ' Σ δ' → coe (Cand Σ & (Ty-ₛ∘ₑ σ' δ' B ⁻¹)) (Tyᴹ B Σ (σ' ₛ∘'ₑ δ') (Con'ᴹₑ δ' σ'ᴹ))))

--------------------------------------------------------------------------------

uCon' : ∀ (Γ' : Con') → Con'ᴹ Γ' {Γ'} id'ₛ
uCon' ∙       = ∙
uCon' (Γ' ,*) = Con'ᴹₑ (drop id'ₑ) (uCon' Γ') , u* vz

uCon'-idₑ : ∀ Γ' → Con'ᴹₑ id'ₑ (uCon' Γ') ≅ uCon' Γ'
uCon'-idₑ ∙       = refl̃
uCon'-idₑ (Γ' ,*) =
   ap3̃ {C = λ _ _ → *ᴹ (var (vz {Γ'}))} (λ σ' → Con'ᴹ, {σ' = σ'})
   (ass'ₛₑₑ id'ₛ wk' (keep id'ₑ) ◾ (id'ₛ ₛ∘'ₑ_) & (drop & idr'ₑ id'ₑ))
   (Con'ᴹ-∘ₑ wk' id'ₑ (uCon' Γ') ⁻¹̃ ◾̃ ap̃ (λ x → Con'ᴹₑ (drop x) (uCon' Γ')) (idr'ₑ id'ₑ))
   (*ᴹ-idₑ (u* vz))

uCon : ∀ Γ' Γ → Conᴹ {Γ'} Γ Γ (uCon' Γ')
uCon ∙      ∙       = ∙
uCon Γ'     (Γ , A) =
  coe (ap2 (λ σ' → Conᴹ Γ (Γ , A) {σ'}) (idr'ₛₑ id'ₛ) (uCon'-idₑ Γ'))
    (Conᴹₑ (drop {A = A} idₑ) (uCon Γ' Γ)) ,
  Tyᴹ A (Γ , A) id'ₛ (uCon' Γ') .U (coe (Ne (Γ , A) & (Ty-idₛ A ⁻¹)) (var vz))

uCon (Γ' ,*) (Γ ,*)  = Conᴹₑ (drop' idₑ) (uCon Γ' Γ) ,*

nf : ∀ {Γ' A Γ} → Tm {Γ'} Γ A → Nf Γ A
nf {Γ'}{A}{Γ} t = coe (Nf Γ & Ty-idₛ A) (Tyᴹ A Γ _ (uCon' Γ') .Q (Tmᴹ t _ (uCon Γ' Γ)))

