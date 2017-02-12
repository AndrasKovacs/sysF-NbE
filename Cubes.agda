
{-# OPTIONS --rewriting --type-in-type #-}

module Cubes where

-- Core definition of cubical equality. A simplification of Conor McBride's "cubical crossroads"
-- presentation.

postulate _↦_ : ∀ {A : Set} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}
infix 3 _↦_

-- Equality
--------------------------------------------------------------------------------

postulate
  I : Set
  ₀ ₁ : I
  _[_-_] : I → I → I → I

infix 3 _≡_
data _≡_ {A : Set} : A → A → Set where
  path : (f : I → A) → f ₀ ≡ f ₁

syntax path (λ i → t) = ⟨ i ⟩ t

_$_ : ∀ {α}{A : Set α}{x y : A} → x ≡ y → I → A
path f $ i = f i
infixl 8 _$_
{-# DISPLAY path f = f #-}

postulate
  $-₀ : (A : Set)(x y : A)(p : x ≡ y) → p $ ₀ ↦ x
  $-₁ : (A : Set)(x y : A)(p : x ≡ y) → p $ ₁ ↦ y
{-# REWRITE $-₀ #-}
{-# REWRITE $-₁ #-}

postulate
  [₀-₀]      : ∀ p   → p [ ₀ - ₀ ] ↦ ₀
  [₀-₁]      : ∀ p   → p [ ₀ - ₁ ] ↦ p
  [₁-₁]      : ∀ p   → p [ ₁ - ₁ ] ↦ ₁
  [-]-left   : ∀ q r → ₀ [ q - r ] ↦ q
  [-]-right  : ∀ q r → ₁ [ q - r ] ↦ r
  path-η     : (A : Set) (S T : A) (Q : S ≡ T) → ⟨ i ⟩ (Q $ i) ↦ Q
{-#  REWRITE [₀-₀]     #-}
{-#  REWRITE [₀-₁]     #-}
{-#  REWRITE [₁-₁]     #-}
{-#  REWRITE [-]-left  #-}
{-#  REWRITE [-]-right #-}
{-#  REWRITE path-η    #-}

1- : I → I
1- i = i [ ₁ - ₀ ]

infixr 4 _◾_
postulate
  _◾_        : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  coe        : {A B : Set} → A ≡ B → A → B
  regularity : (A : Set)(p : A ≡ A) → coe p ↦ (λ a → a)
{-# REWRITE regularity #-}

postulate
  coe-Π :
    (A : I → Set)(B : (i : I) → A i → Set)(f : (a : A ₀) → B ₀ a)
    → coe (⟨ i ⟩ ((a : A i) → B i a)) f
      ↦
      (λ a → coe (⟨ i ⟩ B i (coe (⟨ j ⟩ A (j [ ₁ - i ])) a ))
                 (f (coe (⟨ i ⟩ A (1- i)) a)))

  coe-≡ :
      (A : I → Set)(x y : ∀ i → A i)(p : x ₀ ≡ y ₀)
    → coe (⟨ i ⟩ (_≡_ {A i} (x i) (y i))) p ↦
       ⟨ i ⟩ coe (⟨ j ⟩ (A (i [ ₁ - j ]))) (x (1- i))
     ◾ ⟨ i ⟩ coe (path A) (p $ i)
     ◾ ⟨ i ⟩ coe (⟨ j ⟩ (A (i [ j - ₁ ]))) (y i)

  coe-◾  : (A B C : Set)(p : A ≡ B)(q : B ≡ C) → coe (p ◾ q) ↦ (λ a → coe q (coe p a))
  refl-◾ : (A : Set)(x y : A)(p : x ≡ y) → (⟨ _ ⟩ x) ◾ p ↦ p
  ◾-refl : (A : Set)(x y : A)(p : x ≡ y) → p ◾ (⟨ _ ⟩ y) ↦ p

{-# REWRITE coe-Π  #-}
{-# REWRITE coe-◾ #-}
{-# REWRITE refl-◾ #-}
{-# REWRITE ◾-refl #-}
{-# REWRITE coe-≡ #-}

-- Derived ops
--------------------------------------------------------------------------------

refl : {A : Set}{a : A} → a ≡ a
refl {_}{a} = ⟨ _ ⟩ a

J : {A : Set}{a : A}(P : ∀ a' → a ≡ a' → Set) → P a refl → ∀ {a'} (p : a ≡ a') → P a' p
J P refl* p = coe (⟨ i ⟩ P (p $ i) (⟨ j ⟩ (p $ i [ ₀ - j ]))) refl*

infix 5 _⁻¹
_⁻¹ : ∀ {A : Set}{x y : A} → x ≡ y → y ≡ x
_⁻¹ p = ⟨ i ⟩ (p $ 1- i)

eq-inv : ∀ {A}{a b : A}(p : a ≡ b) → p ◾ p ⁻¹ ≡ refl
eq-inv p = J (λ _ p → p ◾ p ⁻¹ ≡ refl) refl p

infixl 9 _&_
_&_ : {A : Set}{B : Set}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
_&_ f p = ⟨ i ⟩ f (p $ i)

ext : {A : Set}{B : A → Set}{f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g
ext {f = f} {g} p = ⟨ i ⟩ (λ a → p a $ i)

exti :
  ∀ {A : Set}{B : A → Set}{f g : ∀ {a} → B a}
  → (∀ a → f {a} ≡ g {a}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
exti {f = f}{g} p = ⟨ i ⟩ (λ {a} → p a $ i)

infixl 8 _⊗_
_⊗_ : ∀ {A B}{f g : A → B}(p : f ≡ g){a a' : A}(q : a ≡ a') → f a ≡ g a'
p ⊗ q = ⟨ i ⟩ (p $ i) (q $ i)

apd2' :
  {A : Set}{a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  {B : A → Set}{C : Set}
  (f : ∀ a → B a → C){b₀ : B a₀}{b₁ : B a₁}
  (b₂ : coe (B & a₂) b₀ ≡ b₁) → f a₀ b₀ ≡ f a₁ b₁
apd2' {A}{a₀}{a₁} = J (λ a₁ (a₂ : a₀ ≡ a₁) → {B : A → Set}{C : Set}
  (f : ∀ a → B a → C){b₀ : B a₀}{b₁ : B a₁}
  (b₂ : coe (B & a₂) b₀ ≡ b₁) → f a₀ b₀ ≡ f a₁ b₁) (λ f b₂ → f a₀ & b₂) {a₁}
