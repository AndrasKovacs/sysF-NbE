{-# OPTIONS --without-K --rewriting --type-in-type #-}

module Lib where

open import Cubes public

--------------------------------------------------------------------------------

infix 3 _∋_
_∋_ : (A : Set) → A → A
A ∋ a = a

_∘_ : ∀ {A : Set} {B : A → Set} {C : {x : A} → B x → Set} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

--------------------------------------------------------------------------------

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
infixr 5 _,_

∃ : {A : Set} → (A → Set) → Set
∃ = Σ _

∃₂ : {A : Set}{B : A → Set}(C : (x : A) → B x → Set) → Set
∃₂ C = ∃ λ a → ∃ λ b → C a b

open Σ public

_×_ : Set → Set → Set
A × B = Σ A λ _ → B
infixr 4 _×_

postulate
  coe-Σ :
    (A : I → Set)(B : ∀ i → A i → Set)
    → coe (⟨ i ⟩ (Σ (A i) (B i))) ↦ (λ (p : Σ (A ₀) (B ₀)) → 
       ((coe (path A) (proj₁ p)) ,
       coe (⟨ i ⟩ B i (coe (⟨ j ⟩ A (j [ ₀ - i ])) (proj₁ p))) (proj₂ p)))
{-# REWRITE coe-Σ #-}       

--------------------------------------------------------------------------------

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

--------------------------------------------------------------------------------

apd2' :
  {A : Set}{a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  {B : A → Set}{C : Set}
  (f : ∀ a → B a → C){b₀ : B a₀}{b₁ : B a₁}
  (b₂ : coe (B & a₂) b₀ ≡ b₁) → f a₀ b₀ ≡ f a₁ b₁
apd2' {A}{a₀}{a₁} = J (λ a₁ (a₂ : a₀ ≡ a₁) →   {B : A → Set}{C : Set}
  (f : ∀ a → B a → C){b₀ : B a₀}{b₁ : B a₁}
  (b₂ : coe (B & a₂) b₀ ≡ b₁) → f a₀ b₀ ≡ f a₁ b₁) (λ f b₂ → f a₀ & b₂) {a₁}

Π-≡ :
    ∀ {A A' : Set} → (p : A ≡ A')
  → ∀ {B : A → Set}{B' : A' → Set} → ((a : A) → B a ≡ B' (coe p a)) 
  → ((a : A) → B a) ≡ ((a' : A') → B' a')
Π-≡ {A} {A'} = J (λ A' (p : A ≡ A') → ∀ {B : A → Set}{B' : A' → Set} → ((a : A) → B a ≡ B' (coe p a)) 
               → ((a : A) → B a) ≡ ((a' : A') → B' a')) (λ q → ⟨ i ⟩ ((a : A) → q a $ i)) {A'}

