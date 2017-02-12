{-# OPTIONS --rewriting --type-in-type #-}

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
open Σ public    
infixr 5 _,_

∃ : {A : Set} → (A → Set) → Set
∃ = Σ _

∃₂ : {A : Set}{B : A → Set}(C : (x : A) → B x → Set) → Set
∃₂ C = ∃ λ a → ∃ λ b → C a b

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

-- HEq
--------------------------------------------------------------------------------
record _≅_ {A B : Set}(a : A)(b : B) : Set where
  constructor con
  field
    ty : A ≡ B
    tm : coe ty a ≡ b
open _≅_ public

uncoe : ∀ {A B}(p : A ≡ B) a → a ≅ coe p a
uncoe p a = con p refl

refl̃ : ∀ {A}{a : A} → a ≅ a
refl̃ = con refl refl

infix 5 _⁻¹̃ 
_⁻¹̃ : ∀ {A B}{a : A}{b : B} → a ≅ b → b ≅ a
_⁻¹̃ {A} {B} {a} {b} (con ty tm) =
  con (ty ⁻¹) (coe (ty ⁻¹) & tm ⁻¹ ◾ (λ p → coe p a) & eq-inv ty)

infixr 4 _◾̃_ 
_◾̃_ : ∀ {A B C}{a : A}{b : B}{c : C} → a ≅ b → b ≅ c → a ≅ c
con ty tm ◾̃ con ty' tm' = con (ty ◾ ty') (coe ty' & tm ◾ tm')

sub̃ : ∀ {A}(P : A → Set)(f : ∀ a → P a){a₀ a₁ : A}(a₂ : a₀ ≡ a₁) → f a₀ ≅ f a₁
sub̃ P f a₂ = con (P & a₂) (⟨ i ⟩ coe (⟨ j ⟩ P (a₂ $ i [ j - ₁ ])) (f (a₂ $ i)))

uñ : ∀ {A}{a b : A} → a ≅ b → a ≡ b
uñ (con ty tm) = tm


