
module Lib where

open import Level

--------------------------------------------------------------------------------

id : ∀ {α}{A : Set α} → A → A
id a = a

infixr 9 _∘_
_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

infixl 0 _∋_
_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ x = x

-- Eq
--------------------------------------------------------------------------------

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

J : ∀{α β}{A : Set α}{a : A}(P : ∀ a' → a ≡ a' → Set β) → P a refl → ∀ {a'} (p : a ≡ a') → P a' p
J P refl' refl = refl'

coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
coe refl a = a

infix 6 _⁻¹
infixr 5 _◾_

_⁻¹ : ∀ {α}{A : Set α}{a b : A} → a ≡ b → b ≡ a
refl ⁻¹ = refl

_◾_ : ∀ {α}{A : Set α}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ◾ q = q

eq-inv : ∀ {α}{A : Set α}{a b : A}(p : a ≡ b) → p ◾ p ⁻¹ ≡ refl
eq-inv p = J (λ _ p → p ◾ p ⁻¹ ≡ refl) refl p

infixl 9 _&_
_&_ : ∀{α β}{A : Set α}{B : Set β}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
f & refl = refl

postulate
  ext : ∀{α β}{A : Set α}{B : A → Set β}{f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g
  exti :
    ∀ {α}{β}{A : Set α}{B : A → Set β}{f g : ∀ {a} → B a}
    → (∀ a → f {a} ≡ g {a}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})

infixl 8 _⊗_
_⊗_ : ∀ {α}{A B : Set α}{f g : A → B}(p : f ≡ g){a a' : A}(q : a ≡ a') → f a ≡ g a'
refl ⊗ refl = refl

ap2 :
  ∀{α β γ}{A : Set α}{a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  {B : A → Set β}{C : Set γ}
  (f : ∀ a → B a → C){b₀ : B a₀}{b₁ : B a₁}
  (b₂ : coe (B & a₂) b₀ ≡ b₁) → f a₀ b₀ ≡ f a₁ b₁
ap2 refl f refl = refl

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

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

-- HEq
--------------------------------------------------------------------------------
record _≅_ {α}{A B : Set α}(a : A)(b : B) : Set (suc α) where
  field
    ty : A ≡ B
    tm : coe ty a ≡ b
open _≅_ public

uncoe : ∀ {α}{A B : Set α}(p : A ≡ B) a → a ≅ coe p a
uncoe p a = record {ty = p; tm = refl}

pattern refl̃ = record {ty = refl; tm = refl}

infix 6 _⁻¹̃ 
_⁻¹̃ : ∀ {α}{A B : Set α}{a : A}{b : B} → a ≅ b → b ≅ a
refl̃ ⁻¹̃ = refl̃

infixr 5 _◾̃_ 
_◾̃_ : ∀ {α}{A B C : Set α}{a : A}{b : B}{c : C} → a ≅ b → b ≅ c → a ≅ c
refl̃ ◾̃ q = q

sub̃ : ∀ {α β}{A : Set α}(P : A → Set β)(f : ∀ a → P a){a₀ a₁ : A}(a₂ : a₀ ≡ a₁) → f a₀ ≅ f a₁
sub̃ P f refl = refl̃

-- TODO: disable K, require {{IsSet}} here
uñ : ∀ {α}{A : Set α}{a b : A} → a ≅ b → a ≡ b
uñ refl̃ = refl

