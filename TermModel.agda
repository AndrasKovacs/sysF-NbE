
{-# OPTIONS --without-K --type-in-type #-}

module TermModel where

open import Lib
open import Type
open import Term
open import TypeModel

--------------------------------------------------------------------------------

data Conᴹ : ∀ {Γ'} → Con Γ' → ∀ {Δ'} (Δ : Con Δ'){σ'} → Con'ᴹ Γ' {Δ'} σ' → Set where
  ∙   : ∀ {Δ' Δ} → Conᴹ ∙ {Δ'} Δ ∙
  _,_ : ∀ {Γ' Γ Δ' Δ σ' σ'ᴹ A} → Conᴹ {Γ'} Γ {Δ'} Δ {σ'} σ'ᴹ → Tyᴹ A Δ σ' σ'ᴹ .S → Conᴹ (Γ , A) Δ σ'ᴹ
  _,* : ∀ {Γ' Γ Δ' Δ σ' σ'ᴹ A}{Aᴹ : *ᴹ A} → Conᴹ {Γ'} Γ {Δ'} Δ {σ'} σ'ᴹ → Conᴹ (Γ ,*) Δ (σ'ᴹ , Aᴹ)

Conᴹₑ :
  ∀ {Γ' Γ Δ' Δ σ' σ'ᴹ Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ) → Conᴹ {Γ'} Γ Δ {σ'} σ'ᴹ → Conᴹ Γ Σ (Con'ᴹₑ δ' σ'ᴹ)
Conᴹₑ δ ∙ = ∙
Conᴹₑ δ (_,_ {A = A} Γᴹ tᴹ) = Conᴹₑ δ Γᴹ , Tyᴹₑ A _ δ tᴹ
Conᴹₑ δ (Γᴹ ,*) = Conᴹₑ δ Γᴹ ,*

∈ᴹ : ∀ {Γ' Γ A} → _∈_ {Γ'} A Γ → ∀ {Δ' Δ σ'} σ'ᴹ → Conᴹ Γ Δ σ'ᴹ → Tyᴹ {Γ'} A {Δ'} Δ σ' σ'ᴹ .S
∈ᴹ vz       σ'ᴹ      (Γᴹ , t) = t
∈ᴹ (vs v)   σ'ᴹ      (Γᴹ , t) = ∈ᴹ v σ'ᴹ Γᴹ
∈ᴹ (vs* {A = B} v) {Δ = Δ} (_,_ {σ' = σ'} {A} σ'ᴹ x) (Γᴹ ,*) =
  coe (ap2 (λ x y → Tyᴹ B Δ x y .S) (idl'ₑₛ σ' ⁻¹) (OPE'ᴹ-id σ'ᴹ ⁻¹̃) ◾ Tyₑᴹ B Δ wk' (σ'ᴹ , x) ⁻¹)
    (∈ᴹ v σ'ᴹ Γᴹ)

Tmᴹ : ∀ {Γ' Γ A} → Tm {Γ'} Γ A → ∀ {Δ' Δ σ'} σ'ᴹ → Conᴹ Γ Δ σ'ᴹ → Tyᴹ {Γ'} A {Δ'} Δ σ' σ'ᴹ .S
Tmᴹ (var v)    σ'ᴹ Γᴹ = ∈ᴹ v σ'ᴹ Γᴹ
Tmᴹ (lam t)    σ'ᴹ Γᴹ = λ δ aᴹ → Tmᴹ t _ (Conᴹₑ δ Γᴹ , aᴹ)

Tmᴹ {A = B} (app {A} f x) {Δ = Δ} {σ'} σ'ᴹ Γᴹ =
  coe (ap2 (λ x y → Tyᴹ B Δ x y .S) (idr'ₛₑ σ') (Con'ᴹ-idₑ σ'ᴹ))
    (Tmᴹ f σ'ᴹ Γᴹ idₑ
      (coe (ap2 (λ x y → Tyᴹ A Δ x y .S) (idr'ₛₑ σ' ⁻¹) (Con'ᴹ-idₑ σ'ᴹ ⁻¹̃))
        (Tmᴹ x σ'ᴹ Γᴹ)))

Tmᴹ (tlam t) σ'ᴹ Γᴹ = λ δ B Bᴹ → Tmᴹ t (_ , Bᴹ) (Conᴹₑ δ Γᴹ ,*)

Tmᴹ (tapp {A} t B) {Δ = Δ} {σ'} σ'ᴹ Γᴹ =
  coe ( ap2 (λ x y → Tyᴹ A Δ (x , Tyₛ σ' B) (y , Ty*ᴹ B σ'ᴹ) .S)
        (idr'ₛₑ σ' ◾ idl'ₛ σ' ⁻¹) (Con'ᴹ-idₑ σ'ᴹ ◾̃ {!!})
      ◾ Tyₛᴹ A Δ (id'ₛ , B) σ'ᴹ ⁻¹)
    (Tmᴹ t σ'ᴹ Γᴹ idₑ (Tyₛ σ' B) (Ty*ᴹ B σ'ᴹ))

