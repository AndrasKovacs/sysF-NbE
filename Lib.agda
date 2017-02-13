
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
  constructor con
  field
    ty : A ≡ B
    tm : coe ty a ≡ b
open _≅_ public

infix 5 _~
pattern _~ p = record {ty = refl; tm = p}
pattern refl̃ = refl ~

uncoe : ∀ {α}{A B : Set α}(p : B ≡ A) (b : B) → coe p b ≅ b
uncoe refl a = refl̃

infix 6 _⁻¹̃ 
_⁻¹̃ : ∀ {α}{A B : Set α}{a : A}{b : B} → a ≅ b → b ≅ a
refl̃ ⁻¹̃ = refl̃

infixr 5 _◾̃_ 
_◾̃_ : ∀ {α}{A B C : Set α}{a : A}{b : B}{c : C} → a ≅ b → b ≅ c → a ≅ c
refl̃ ◾̃ q = q

ap̃ :
  ∀ {α β}{A : Set α}{B : A → Set β}
  (f : ∀ a → B a){a₀ a₁ : A}(a₂ : a₀ ≡ a₁) → f a₀ ≅ f a₁
ap̃ f refl = refl̃

ap2̃ :
  ∀ {α β γ}
  {A : Set α}{B : A → Set β}{C : ∀ a → B a → Set γ}
  (f : ∀ a → (b : B a) → C a b)
  {a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≅ b₁) → f a₀ b₀ ≅ f a₁ b₁
ap2̃ f refl refl̃ = refl̃

ap3̃ :
  ∀ {α β γ δ}
  {A : Set α}{B : A → Set β}{C : ∀ a (b : B a) → Set γ}{D : ∀ a (b : B a)(c : C a b) → Set δ}
  (f : ∀ a b c → D a b c)
  {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  {b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≅ b₁)
  {c₀ : C a₀ b₀}{c₁ : C a₁ b₁}(c₂ : c₀ ≅ c₁)
  → f a₀ b₀ c₀ ≅ f a₁ b₁ c₁
ap3̃ f refl refl̃ refl̃ = refl̃

ap4̃ :
  ∀ {α β γ δ ε}
  {A : Set α}{B : A → Set β}{C : ∀ a (b : B a) → Set γ}
    {D : ∀ a b (c : C a b) → Set δ}{E : ∀ a b c (d : D a b c) → Set ε}
  (f : ∀ a b c d → E a b c d)
  {a₀ a₁ : A}                        (a₂ : a₀ ≡ a₁)
  {b₀ : B a₀}      {b₁ : B a₁}       (b₂ : b₀ ≅ b₁)
  {c₀ : C a₀ b₀}   {c₁ : C a₁ b₁}    (c₂ : c₀ ≅ c₁)
  {d₀ : D a₀ b₀ c₀}{d₁ : D a₁ b₁ c₁} (d₂ : d₀ ≅ d₁)  
  → f a₀ b₀ c₀ d₀ ≅ f a₁ b₁ c₁ d₁
ap4̃ f refl refl̃ refl̃ refl̃ = refl̃    

uñ : ∀ {α}{A : Set α}{a b : A} → a ≅ b → a ≡ b
uñ refl̃ = refl

ap2 :
  ∀{α β γ}{A : Set α}{B : A → Set β}{C : Set γ}
  (f : ∀ a → B a → C)
  {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  {b₀ : B a₀}{b₁ : B a₁}(b₂ : b₀ ≅ b₁)
  → f a₀ b₀ ≡ f a₁ b₁
ap2 f refl refl̃ = refl

Π-≡ :
  ∀ {α β}{A : Set α}{B₀ B₁ : A → Set β}
  → (B₂ : ∀ a → B₀ a ≡ B₁ a)
  → (∀ a → B₀ a) ≡ (∀ a → B₁ a)
Π-≡ B₂ = (λ B → ∀ a → B a) & ext B₂

Πi-≡ :
  ∀ {α β}{A : Set α}{B₀ B₁ : A → Set β}
  → (B₂ : ∀ a → B₀ a ≡ B₁ a)
  → (∀ {a} → B₀ a) ≡ (∀ {a} → B₁ a)
Πi-≡ B₂ = (λ B → ∀ {a} → B a) & ext B₂

ext̃ :
  ∀ {α β}
    {A : Set α}
    {B₀ B₁ : A → Set β}
    {f₀ : ∀ a → B₀ a}{f₁ : ∀ a → B₁ a}
  → (∀ a → f₀ a ≅ f₁ a)
  → f₀ ≅ f₁
ext̃ {A = A} {B₀} {B₁} {f₀} {f₁} f₂ =
  J (λ B₁ (B₂ : B₀ ≡ B₁) →
          {f₀ : ∀ a → B₀ a}{f₁ : ∀ a → B₁ a}
        → (∀ a → f₀ a ≅ f₁ a)
        → f₀ ≅ f₁)
     (λ {f₀}{f₁} f₂ → ext (λ a → uñ (f₂ a)) ~)
     (ext (λ a → f₂ a .ty)) f₂

