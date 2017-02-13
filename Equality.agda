{-# OPTIONS --without-K #-}

module Equality where

open import Lib

Π-≡ :
  ∀ {α β}{A₀ A₁ : Set α}{B₀ : A₀ → Set β}{B₁ : A₁ → Set β}
  → (A₂ : A₀ ≡ A₁)
  → (B₂ : ∀ a → B₀ a ≡ B₁ (coe A₂ a))
  → ((a : A₀) → B₀ a) ≡ ((a : A₁) → B₁ a)
Π-≡ refl B₂ = (λ B → ∀ a → B a) & ext B₂

