
{-# OPTIONS --without-K --type-in-type #-}

module TypeModel where

open import Lib
open import Type
open import Term

-- Consider : equality constructor helpers

-- Universe
--------------------------------------------------------------------------------

record QU {Γ'} Γ A S : Set where
  constructor con
  field
    Q : S → Nf {Γ'} Γ A
    U : Ne Γ A → S
open QU

record Cand {Γ'} Γ A : Set where
  constructor con
  field
    S : Set
    P : QU {Γ'} Γ A S
open Cand

pattern cand s q u = Cand.con s (QU.con q u)

*ᴹobjT : ∀ {Γ'}(A : Ty Γ') → Set
*ᴹobjT A = ∀ Δ' Δ σ' → Cand {Δ'} Δ (Tyₑ σ' A)

*ᴹmorphT : ∀ {Γ' A}(o : *ᴹobjT {Γ'} A) → Set
*ᴹmorphT o = ∀ {Δ' Δ σ' Σ'} Σ δ' (δ : OPE {Σ'}{Δ'} δ' Σ Δ) → S (o Δ' Δ σ') → S (o Σ' Σ (σ' ∘'ₑ δ'))

record *ᴹ {Γ'} (A : Ty Γ') : Set where
  constructor con
  field
    obj   : *ᴹobjT A
    morph : *ᴹmorphT obj
open *ᴹ public

u* : ∀ {Γ'}(v : *∈ Γ') → *ᴹ {Γ'} (var v)
u* {Γ'} v = con obj' morph' module u* where
  obj' = λ Δ' Δ σ' → cand (Ne Δ (var (*∈ₑ σ' v))) ne (λ n → n)

  morph' : *ᴹmorphT obj'
  morph' {Δ'}{Δ}{σ'}{Σ'} Σ δ' δ n = coe E (Neₑ δ n)
    module morph' where abstract E = (Ne Σ ∘ var) & *∈-∘ₑ σ' δ' v

*ᴹₑ : ∀ {Γ' Δ' A}(σ' : OPE' Δ' Γ') → *ᴹ {Γ'} A → *ᴹ (Tyₑ σ' A)
*ᴹₑ {Γ'} {Δ'} {A} σ' (con obj morph) = con obj' morph' module *ᴹₑ where
  obj' : *ᴹobjT (Tyₑ σ' A)
  obj' Σ' Σ δ' = con (obj Σ' Σ (σ' ∘'ₑ δ') .S) (coe E (obj Σ' Σ (σ' ∘'ₑ δ') .P))
    module obj' where abstract E = (λ x → QU Σ x (S (obj Σ' Σ (σ' ∘'ₑ δ')))) & (Ty-∘ₑ σ' δ' A ⁻¹)

  morph' : *ᴹmorphT obj'
  morph' {Σ'}{Σ}{δ'}{Ξ'} Ξ ν' ν x = coe E (morph Ξ ν' ν x)
    module morph' where abstract E = (S ∘ obj Ξ' Ξ) & ass'ₑ σ' δ' ν'

abstract
  *ᴹ-idₑ : ∀ {Γ' A} (Aᴹ : *ᴹ {Γ'} A) → *ᴹₑ id'ₑ Aᴹ ≅ Aᴹ
  *ᴹ-idₑ {Γ'} {A} (con obj morph) =
    ap3̃ (λ A → *ᴹ.con {A = A})
      (Ty-idₑ A)
      (ext̃ λ Σ' → ext̃ λ Σ → ext̃ λ σ' →
        ap3̃ (λ A → Cand.con {A = A})
          (Tyₑ σ' & Ty-idₑ A)
          (ap̃ (S ∘ obj Σ' Σ) (idl'ₑ σ'))
          (uncoe (*ᴹₑ.obj'.E _ _ _ _ _ _) _ ◾̃ ap̃ (P ∘ obj Σ' Σ) (idl'ₑ σ')))
      (extĩ λ Σ' → extĩ λ Σ → extĩ λ δ' →
        extĩ λ Ξ' → ext̃ λ Ξ → ext̃ λ ν' → ext̃ λ ν →
        ext̃' ((S ∘ obj Σ' Σ) & idl'ₑ δ') (λ x₀ x₁ x₂ →
            uncoe (*ᴹₑ.morph'.E id'ₑ _ _ _ _ _ _) _
          ◾̃ ap2̃ (λ σ' → morph {σ' = σ'} Ξ ν' ν) (idl'ₑ δ') x₂))

  *ᴹ-∘ₑ :
    ∀ {Γ' Δ' Σ'}{A : Ty Γ'} (σ' : OPE' Δ' Γ') (δ' : OPE' Σ' Δ') (Aᴹ : *ᴹ {Γ'} A)
    → *ᴹₑ (σ' ∘'ₑ δ') Aᴹ ≅ *ᴹₑ δ' (*ᴹₑ σ' Aᴹ)
  *ᴹ-∘ₑ {Γ'} {Δ'} {Σ'} {A} σ' δ' (con obj morph) =
    ap3̃ (λ A → *ᴹ.con {A = A})
      (Ty-∘ₑ σ' δ' A ⁻¹)
      (ext̃ λ Σ' → ext̃ λ Σ → ext̃ λ ν' →
        ap3̃ (λ A → Cand.con {A = Tyₑ ν' A})
          (Ty-∘ₑ σ' δ' A ⁻¹ )
          (ap̃ (S ∘ obj Σ' Σ) (ass'ₑ σ' δ' ν'))
          (  uncoe (*ᴹₑ.obj'.E _ _ _ _ _ _) _
           ◾̃ ap̃ (P ∘ obj Σ' Σ) (ass'ₑ σ' δ' ν')
           ◾̃ uncoe (*ᴹₑ.obj'.E _ _ _ _ _ _) _ ⁻¹̃
           ◾̃ uncoe (*ᴹₑ.obj'.E _ _ _ _ _ _) _ ⁻¹̃))
      (extĩ λ Σ' → extĩ λ Σ → extĩ λ ν' →
       extĩ λ Ξ' → ext̃ λ Ξ → ext̃ λ ε' → ext̃ λ ε →
       ext̃' ((S ∘ obj Σ' Σ) & ass'ₑ σ' δ' ν') (λ x₀ x₁ x₂ →
           uncoe (*ᴹₑ.morph'.E _ _ _ _ _ _ _) _
         ◾̃ ap2̃ (λ σ'' → morph {σ' = σ''} Ξ ε' ε)
             (ass'ₑ σ' δ' ν')
             x₂
         ◾̃ uncoe (*ᴹₑ.morph'.E _ _ _ _ _ _ _) _ ⁻¹̃
         ◾̃ uncoe (*ᴹₑ.morph'.E _ _ _ _ _ _ _) _ ⁻¹̃))

-- Kind contexts
--------------------------------------------------------------------------------

data Con'ᴹ : (Γ' : Con') → ∀ {Δ'} → Sub' Δ' Γ' → Set where
  ∙   : ∀ {Δ'} → Con'ᴹ ∙ {Δ'} ∙
  _,_ : ∀ {Γ' Δ' σ' A} → Con'ᴹ Γ' {Δ'} σ' → *ᴹ A → Con'ᴹ (Γ' ,*) (σ' , A)

Con'ᴹₑ : ∀ {Γ' Δ' σ' Σ'} δ' → Con'ᴹ Γ' {Δ'} σ' → Con'ᴹ Γ' {Σ'} (σ' ₛ∘'ₑ δ')
Con'ᴹₑ δ' ∙          = ∙
Con'ᴹₑ δ' (σ'ᴹ , Aᴹ) = Con'ᴹₑ δ' σ'ᴹ , *ᴹₑ δ' Aᴹ

Con'ᴹ-idₑ : ∀ {Γ' Δ' σ'}(σ'ᴹ : Con'ᴹ Γ' {Δ'} σ') → Con'ᴹₑ id'ₑ σ'ᴹ ≅ σ'ᴹ
Con'ᴹ-idₑ ∙          = refl̃
Con'ᴹ-idₑ {Δ' = Δ'} (_,_ {Γ'} {σ' = σ'} {A} σ'ᴹ Aᴹ) =
  ap4̃ (λ σ' A → Con'ᴹ._,_ {σ' = σ'}{A = A})
    (idr'ₛₑ σ')
    (Ty-idₑ A ~)
    (Con'ᴹ-idₑ σ'ᴹ)
    (*ᴹ-idₑ Aᴹ)

Con'ᴹ-∘ₑ :
  ∀ {Γ' Δ' Σ' Ξ' σ'} δ' (ν' : OPE' Ξ' Σ') σ'ᴹ
  → Con'ᴹₑ {Γ'}{Δ'}{σ'}{Ξ'} (δ' ∘'ₑ ν') σ'ᴹ ≅ Con'ᴹₑ ν' (Con'ᴹₑ δ' σ'ᴹ)
Con'ᴹ-∘ₑ δ' ν' ∙  = refl̃
Con'ᴹ-∘ₑ δ' ν' (_,_ {Γ'} {σ' = σ'} {A} σ'ᴹ Aᴹ) =
  ap4̃ (λ σ' A → Con'ᴹ._,_ {σ' = σ'}{A = A})
    (ass'ₛₑₑ σ' δ' ν' ⁻¹)
    (Ty-∘ₑ δ' ν' A ⁻¹ ~)
    (Con'ᴹ-∘ₑ δ' ν' σ'ᴹ)
    (*ᴹ-∘ₑ δ' ν' Aᴹ)

-- Types
--------------------------------------------------------------------------------

*∈ᴹ : ∀ {Γ'}(v : *∈ Γ') → ∀ {Δ'} Δ (σ : Sub' Δ' Γ')(σᴹ : Con'ᴹ Γ' σ) → Cand Δ (*∈ₛ σ v)
*∈ᴹ vz     Δ (σ , A) (σᴹ , Aᴹ) =
  let con s p = Aᴹ .obj _ Δ id'ₑ in con s (coe E p)
  module *∈ᴹ where abstract E = (λ A → QU Δ A _) & Ty-idₑ A
*∈ᴹ (vs v) Δ (σ , _) (σᴹ , _ ) = *∈ᴹ v Δ σ σᴹ

*∈ᴹₑ :
  ∀ {Γ' v Δ' Δ σ' σ'ᴹ Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ)
  → *∈ᴹ {Γ'} v Δ σ' σ'ᴹ .S → *∈ᴹ v Σ _ (Con'ᴹₑ δ' σ'ᴹ) .S
*∈ᴹₑ {v = vz {Γ'}}{Δ'}{Δ}{σ' , A}{σ'ᴹ , x} {Σ'} {Σ} {δ'} δ aᴹ =
  coe E (x .morph Σ δ' δ aᴹ)
  module *∈ᴹₑ where abstract E = (S ∘ obj x Σ' Σ) & (idl'ₑ δ' ◾ idr'ₑ δ' ⁻¹)
*∈ᴹₑ {v = vs v}{σ'ᴹ = σ'ᴹ , x} δ aᴹ = *∈ᴹₑ{v = v}{σ'ᴹ = σ'ᴹ} δ aᴹ

Tyᴹ : ∀ {Γ'}(A : Ty Γ') → ∀ {Δ'} Δ (σ' : Sub' Δ' Γ')(σ'ᴹ : Con'ᴹ Γ' σ') → Cand Δ (Tyₛ σ' A)
Tyᴹ (var v) σ' σ'ᴹ = *∈ᴹ v σ' σ'ᴹ

Tyᴹ {Γ'} (A ⇒ B) {Δ'} Δ σ' σ'ᴹ = cand S' Q' U' module Tyᴹ₁ where
  S' = ∀ {Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ) → Tyᴹ A Σ _ (Con'ᴹₑ δ' σ'ᴹ) .S → Tyᴹ B Σ _ (Con'ᴹₑ δ' σ'ᴹ) .S

  Q' : S' → Nf Δ (Tyₛ σ' A ⇒ Tyₛ σ' B)
  Q' fᴹ = let σ'ᴹ' = Con'ᴹₑ id'ₑ σ'ᴹ in
    lam (coe E (Tyᴹ B _ _ σ'ᴹ' .P .Q (fᴹ (drop idₑ) (Tyᴹ A _ _ σ'ᴹ' .P .U (var vz)))))
    module Q' where abstract E = (λ x → Nf (Δ , Tyₛ x A) (Tyₛ x B)) & idr'ₛₑ σ'

  U' : Ne Δ (Tyₛ σ' A ⇒ Tyₛ σ' B) → S'
  U' n {Σ'}{Σ}{δ'} δ aᴹ = let σ'ᴹ' = Con'ᴹₑ δ' σ'ᴹ in
    Tyᴹ B _ _ σ'ᴹ' .P .U (app (coe E (Neₑ δ n)) (Tyᴹ A _ _ σ'ᴹ' .P .Q aᴹ))
    module U' where abstract E = Ne Σ & Ty-ₛ∘ₑ σ' δ' (A ⇒ B)

Tyᴹ {Γ'} (∀' A) {Δ'} Δ σ' σ'ᴹ = cand S' Q' U' module Tyᴹ₂ where
  S' = ∀ {Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ) (B : Ty Σ')(Bᴹ : *ᴹ B) → Tyᴹ A Σ _ (Con'ᴹₑ δ' σ'ᴹ , Bᴹ) .S

  Q' : S' → Nf Δ (∀' (Tyₛ (keep'ₛ σ') A))
  Q' fᴹ = tlam (Tyᴹ A _ _ (Con'ᴹₑ wk' σ'ᴹ , u* vz) .P .Q (fᴹ (drop' idₑ) _ (u* vz)))

  U' : Ne Δ (∀' (Tyₛ (keep'ₛ σ') A)) → S'
  U' n {Σ'}{Σ}{δ'} δ B Bᴹ =
    Tyᴹ A _ _ (Con'ᴹₑ δ' σ'ᴹ , Bᴹ) .P .U (coe E (tappₙₑ (Neₑ δ n) B))
    module U' where
      abstract
        E = Ne Σ &
            (Ty-ₑ∘ₛ (keep δ') (id'ₛ , B) (Tyₛ (keep'ₛ σ') A)
          ◾ Ty-∘ₛ (keep'ₛ σ') ((δ' ₑ∘'ₛ id'ₛ) , B) A
          ◾ (λ x → Tyₛ (x , B) A) &
               (ass'ₛₑₛ σ' (drop id'ₑ) ((δ' ₑ∘'ₛ id'ₛ) , B)
             ◾ ((λ x → σ' ∘'ₛ id'ₑ ₑ∘'ₛ x) & idr'ₑₛ δ')
             ◾ (σ' ∘'ₛ_) & idl'ₑₛ (emb'ₑ δ')
             ◾ emb'-∘ₛ σ' δ'))

Tyᴹₑ :
  ∀ {Γ'} A {Δ' Δ σ'} σ'ᴹ {Σ' Σ δ'}(δ : OPE {Σ'}{Δ'} δ' Σ Δ)
  → Tyᴹ {Γ'} A Δ σ' σ'ᴹ .S → Tyᴹ A Σ _ (Con'ᴹₑ δ' σ'ᴹ) .S
Tyᴹₑ (var v) σ'ᴹ δ aᴹ = *∈ᴹₑ {v = v} δ aᴹ

Tyᴹₑ {Γ'} (A ⇒ B) {σ' = σ'}  σ'ᴹ {δ' = δ'} δ tᴹ {Σ'} {Σ} {ν'} ν aᴹ =
  coe E1 (tᴹ (δ ∘ₑ ν) (coe E2 aᴹ))
  module Tyᴹₑ₁ where
    abstract
      E1 = ap2 (λ x y → Tyᴹ B Σ x y .S) (ass'ₛₑₑ σ' δ' ν' ⁻¹) (Con'ᴹ-∘ₑ δ' ν' σ'ᴹ)
      E2 = ap2 (λ x y → Tyᴹ A Σ x y .S) (ass'ₛₑₑ σ' δ' ν') (Con'ᴹ-∘ₑ δ' ν' σ'ᴹ ⁻¹̃)

Tyᴹₑ (∀' A) {σ' = σ'} σ'ᴹ {δ' = δ'} δ tᴹ {Ξ'} {Ξ} {ν'} ν B Bᴹ =
  coe E (tᴹ (δ ∘ₑ ν) B Bᴹ)
  module Tyᴹₑ₂ where
    abstract
      E = ap2 (λ x y → Tyᴹ A Ξ x y .S)
        ((_, B) & (ass'ₛₑₑ σ' δ' ν' ⁻¹))
        (ap2̃ (λ σ' σ'ᴹ → Con'ᴹ._,_ {σ' = σ'} σ'ᴹ Bᴹ)
          (ass'ₛₑₑ σ' δ' ν' ⁻¹)
          (Con'ᴹ-∘ₑ δ' ν' σ'ᴹ))

-- Embeddings
--------------------------------------------------------------------------------

OPE'ᴹ : ∀ {Γ' Δ'}(σ' : OPE' Γ' Δ') → ∀ {Σ' δ'} → Con'ᴹ Γ' {Σ'} δ' → Con'ᴹ Δ' {Σ'} (σ' ₑ∘'ₛ δ')
OPE'ᴹ ∙         {Σ'}  δ'ᴹ       = δ'ᴹ
OPE'ᴹ (drop σ') {Σ'} (δ'ᴹ , _)  = OPE'ᴹ σ' δ'ᴹ
OPE'ᴹ (keep σ') {Σ'} (δ'ᴹ , Aᴹ) = OPE'ᴹ σ' δ'ᴹ , Aᴹ

OPE'ᴹ-id : ∀ {Γ' Δ' σ'}(σ'ᴹ : Con'ᴹ Γ' {Δ'} σ') → OPE'ᴹ id'ₑ σ'ᴹ ≅ σ'ᴹ
OPE'ᴹ-id ∙          = refl̃
OPE'ᴹ-id (_,_ {Γ'} {σ' = σ'} σ'ᴹ Aᴹ) =
  ap2̃ (λ σ' σ'ᴹ → Con'ᴹ._,_ {σ' = σ'} σ'ᴹ Aᴹ)
    (idl'ₑₛ σ')
    (OPE'ᴹ-id σ'ᴹ)

OPE'ᴹ-nat :
  ∀ {Γ' Δ' Σ' Ξ' σ'} (δ' : OPE' Δ' Γ') (ν' : OPE' Ξ' Σ') (σ'ᴹ : Con'ᴹ Δ' σ')
  → OPE'ᴹ δ' (Con'ᴹₑ ν' σ'ᴹ) ≅ Con'ᴹₑ ν' (OPE'ᴹ δ' σ'ᴹ)
OPE'ᴹ-nat ∙         ν' σ'ᴹ        = refl̃
OPE'ᴹ-nat (drop δ') ν' (σ'ᴹ , _)  = OPE'ᴹ-nat δ' ν' σ'ᴹ
OPE'ᴹ-nat (keep δ') ν' (σ'ᴹ , Aᴹ) =
  ap2̃ (λ σ' σ'ᴹ → Con'ᴹ._,_ {σ' = σ'} σ'ᴹ (*ᴹₑ ν' Aᴹ))
    (ass'ₑₛₑ δ' _ ν' ⁻¹)
    (OPE'ᴹ-nat δ' ν' σ'ᴹ)

*∈ₑᴹ :
  ∀ {Γ'} v {Δ' Σ'} Σ δ' {σ'} σ'ᴹ
  → *∈ᴹ {Δ'} (*∈ₑ {Γ'} δ' v) {Σ'} Σ σ' σ'ᴹ ≅ *∈ᴹ v Σ (δ' ₑ∘'ₛ σ') (OPE'ᴹ δ' σ'ᴹ)
*∈ₑᴹ v      Σ ∙          σ'ᴹ       = refl̃
*∈ₑᴹ v      Σ (drop δ') (σ'ᴹ , _ ) = *∈ₑᴹ v Σ δ' σ'ᴹ
*∈ₑᴹ (vs v) Σ (keep δ') (σ'ᴹ , Aᴹ) = *∈ₑᴹ v Σ δ' σ'ᴹ
*∈ₑᴹ vz {Σ' = Σ'} Σ (keep δ') (_,_ {σ' = σ'} {A} σ'ᴹ Aᴹ) =
  Cand.con (S (Aᴹ .obj Σ' Σ id'ₑ)) &
    uñ (uncoe (*∈ᴹ.E _ _ _ _ _) _ ◾̃ refl̃ ◾̃ uncoe (*∈ᴹ.E _ _ _ _ _) _ ⁻¹̃) ~

Tyₑᴹ :
  ∀ {Γ'} A {Δ' Σ'} Σ δ' {σ'} σ'ᴹ
  → Tyᴹ {Δ'} (Tyₑ {Γ'} δ' A) {Σ'} Σ σ' σ'ᴹ ≅ Tyᴹ A Σ (δ' ₑ∘'ₛ σ') (OPE'ᴹ δ' σ'ᴹ)
Tyₑᴹ {Γ'} (var v) {Δ'} {Σ'} Σ δ' {σ'} σ'ᴹ = *∈ₑᴹ v Σ δ' σ'ᴹ
Tyₑᴹ {Γ'} (A ⇒ B) {Δ'} {Σ'} Σ δ' {σ'} σ'ᴹ =
  let E1   = Ty-ₑ∘ₛ δ' σ' A
      E2   = Ty-ₑ∘ₛ δ' σ' B
      E3   = _⇒_ & E1 ⊗ E2
      Hyp  = λ {Ξ'}{Ξ}(ν' : OPE' Ξ' Σ') A → Tyₑᴹ A Ξ δ' (Con'ᴹₑ ν' σ'ᴹ)
      E4   =
        λ {Ξ'}{Ξ}(ν' : OPE' Ξ' Σ') A →
          uñ (ap2̃ (λ A → S {A = A}) (Ty-ₑ∘ₛ δ' (σ' ₛ∘'ₑ ν') A) (Hyp ν' A)
            ◾̃ ap2̃ (λ x y → Tyᴹ A Ξ x y .S) (ass'ₑₛₑ δ' σ' ν' ⁻¹) (OPE'ᴹ-nat δ' ν' σ'ᴹ))
      E5 =
        Πi-≡ λ Ξ' → Πi-≡ λ Ξ → Πi-≡ λ ν' → Π-≡ λ ν →
          (λ x y → x → y) & E4 ν' A ⊗ E4 ν' B
  in
    ap3̃ (λ A s (p : QU Σ A s) → Cand.con {A = A} s p) E3 (E5 ~)
      (ap4̃ (λ A s (q : s → Nf Σ A) (u : Ne Σ A → s) → QU.con q u) E3 (E5 ~)
        (ext̃' E5 (λ a₀ a₁ a₂ →
          let E6 = λ A → Ty-ₑ∘ₛ δ' (σ' ₛ∘'ₑ id'ₑ) A ◾ (λ x → Tyₛ x A) & (ass'ₑₛₑ δ' σ' id'ₑ ⁻¹)
          in
            ap3̃ (λ A B → Nf.lam {A = A}{B = B}) E1 (E2 ~)
              (  uncoe (Tyᴹ₁.Q'.E _ _ _ _ _ _) _
               ◾̃
                  ap4̃ (λ A B (c : Cand (Σ , A) B) (x : c .S) → c .P .Q x)
                    (E6 A)
                    (E6 B ~)
                    (   Tyₑᴹ B (Σ , Tyₛ (σ' ₛ∘'ₑ id'ₑ) (Tyₑ δ' A)) δ' (Con'ᴹₑ id'ₑ σ'ᴹ)
                      ◾̃ ap3̃ (λ A σ' σ'ᴹ → Tyᴹ B (Σ , A) σ' σ'ᴹ) (E6 A)
                          ((ass'ₑₛₑ δ' σ' id'ₑ ⁻¹) ~)
                          (OPE'ᴹ-nat δ' id'ₑ σ'ᴹ))
                          {!!}
               ◾̃ uncoe (Tyᴹ₁.Q'.E _ _ _ _ _ _) _ ⁻¹̃)))
        (ext̃' (Ne Σ & E3) (λ b₀ b₁ b₂ →
          extĩ λ Ξ' → extĩ λ Ξ → extĩ λ ν' → ext̃ λ ν →
          ext̃' (E4 ν' A) (λ a₀ a₁ a₂ →
            let E6 =
                  λ A → Ty-ₛ∘ₑ σ' ν' (Tyₑ δ' A) ⁻¹
                      ◾ Tyₑ ν' & Ty-ₑ∘ₛ δ' σ' A
                      ◾ Ty-ₛ∘ₑ (δ' ₑ∘'ₛ σ') ν' A
            in
              ap3̃ (λ A (c : Cand Ξ A) (x : Ne Ξ A) → c .P .U x)
               (E6 B)
               (Hyp ν' B ◾̃ ap2̃ (Tyᴹ B Ξ) (ass'ₑₛₑ δ' σ' ν' ⁻¹) (OPE'ᴹ-nat δ' ν' σ'ᴹ))
               (ap4̃ (λ A B → Ne.app {A = A}{B = B}) (E6 A) (E6 B ~)
                 (   uncoe (Tyᴹ₁.U'.E _ _ _ _ _ _ _ _) _
                   ◾̃ ap2̃ (λ A (n : Ne Σ A) → Neₑ {A = A} ν n) E3 b₂
                   ◾̃ uncoe (Tyᴹ₁.U'.E  _ _ _ _ _ _ _ _) _ ⁻¹̃)
                 (ap3̃ (λ A (c : Cand Ξ A) (a : c .S) → c .P .Q a) (E6 A)
                    (Hyp ν' A ◾̃ ap2̃ (Tyᴹ A Ξ) (ass'ₑₛₑ δ' σ' ν' ⁻¹) (OPE'ᴹ-nat δ' ν' σ'ᴹ))
                    a₂))))))

Tyₑᴹ {Γ'} (∀' A)  {Δ'} {Σ'} Σ δ' {σ'} σ'ᴹ =
  let E1 =   (Ty-ₑ∘ₛ (keep δ') (keep'ₛ σ') A
           ◾ (λ x → Tyₛ (x , var vz) A) & (ass'ₑₛₑ δ' σ' wk' ⁻¹))
      E2 =
        Πi-≡ λ Ξ' → Πi-≡ λ Ξ → Πi-≡ λ ν' → Π-≡ λ ν → Π-≡ λ B → Π-≡ λ Bᴹ →
          uñ
           (ap2̃ (λ A → S {A = A})
              (Ty-ₑ∘ₛ (keep δ') (σ' ₛ∘'ₑ ν' , B) A)
              (Tyₑᴹ A Ξ (keep δ') (Con'ᴹₑ ν' σ'ᴹ , Bᴹ))
           ◾̃ ap2̃ (λ x y → Tyᴹ A Ξ (x , B) (y , Bᴹ) .S)
              (ass'ₑₛₑ δ' σ' ν' ⁻¹)
              (OPE'ᴹ-nat δ' ν' σ'ᴹ))
  in
    ap3̃ (λ A s (p : QU Σ A s) → Cand.con {A = A} s p) (∀' & E1) (E2 ~)
      (ap4̃ (λ A s (q : s → Nf Σ A) (u : Ne Σ A → s) → QU.con q u) (∀' & E1) (E2 ~)
        (ext̃' E2 (λ a₀ a₁ a₂ →
          ap2̃ (λ A → Nf.tlam {A = A}) E1
            (
            ap3̃ (λ A (c : Cand (Σ ,*) A) x → c .P .Q x) E1
             {Tyᴹ (Tyₑ (keep δ') A) (Σ ,*) (σ' ₛ∘'ₑ wk' , var vz)
      (Con'ᴹₑ wk' σ'ᴹ , u* vz)}
             {Tyᴹ A (Σ ,*) ((δ' ₑ∘'ₛ σ') ₛ∘'ₑ wk' , var vz)
      (Con'ᴹₑ wk' (OPE'ᴹ δ' σ'ᴹ) , u* vz)}
             (   Tyₑᴹ A (Σ ,*) (keep δ') (Con'ᴹₑ wk' σ'ᴹ , u* vz)
               ◾̃ ap2̃ (λ x y → Tyᴹ A (Σ ,*) (x , var vz) (y , u* vz))
                   (ass'ₑₛₑ δ' σ' wk' ⁻¹)
                   (OPE'ᴹ-nat δ' wk' σ'ᴹ))
             {(a₀ (drop' idₑ) (var vz) (u* vz))}
             {(a₁ (drop' idₑ) (var vz) (u* vz))}
             {!

             !})))
        (ext̃' (Ne Σ & (∀' & E1)) (λ a₀ a₁ a₂ →
          extĩ λ Ξ' → extĩ λ Ξ → extĩ λ ν' → ext̃ λ ν →
          ext̃ λ B → ext̃ λ Bᴹ →
            ap3̃ (λ A (c : Cand Ξ A) (n : Ne Ξ A) → c .P .U n)
              (   Ty-ₑ∘ₛ (keep δ') (σ' ₛ∘'ₑ ν' , B) A
                ◾ (λ x → Tyₛ (x , B) A) & (ass'ₑₛₑ δ' σ' ν' ⁻¹))
              (   Tyₑᴹ A Ξ (keep δ') (Con'ᴹₑ ν' σ'ᴹ , Bᴹ)
                ◾̃ ap2̃ (λ x y → Tyᴹ A Ξ (x , B) (y , Bᴹ))
                    (ass'ₑₛₑ δ' σ' ν' ⁻¹)
                    (OPE'ᴹ-nat δ' ν' σ'ᴹ))
              (   uncoe (Tyᴹ₂.U'.E _ _ _ _ _ _ _ _) _
                ◾̃
                ap2̃ (λ A (n : Ne Σ (∀' A)) → tappₙₑ (Neₑ ν n) B)
                  (   Ty-ₑ∘ₛ (keep δ') (keep'ₛ σ') A
                    ◾ (λ x → Tyₛ (x , var vz) A) & (ass'ₑₛₑ δ' σ' wk' ⁻¹))
                  a₂
                ◾̃ uncoe (Tyᴹ₂.U'.E _ _ _ _ _ _ _ _) _ ⁻¹̃))))

Tyᴹₑ-shuffle :
  ∀ {Γ' Δ' Σ' Ξ' Ξ Ω' Ω}(σ' : OPE' Γ' Σ'){δ' : Sub' Δ' Γ'} A
    ν' (δ'ᴹ : Con'ᴹ Γ' δ'){ε'} (ε : OPE {Ω'}{Ξ'} ε' Ω Ξ) x₀ x₁ (x₂ : x₀ ≅ x₁)
  → Tyᴹₑ (Tyₑ σ' A) (Con'ᴹₑ ν' δ'ᴹ) ε x₀ ≅ Tyᴹₑ A (Con'ᴹₑ ν' (OPE'ᴹ σ' δ'ᴹ)) ε x₁
Tyᴹₑ-shuffle σ' (var v) ν' δ'ᴹ ε x₀ x₁ x₂ = {!!} -- ?
Tyᴹₑ-shuffle σ' (A ⇒ B) ν' δ'ᴹ ε x₀ x₁ x₂ = {!!} -- ok
Tyᴹₑ-shuffle σ' (∀' A)  ν' δ'ᴹ ε x₀ x₁ x₂ = {!!} -- ok

-- Extending Tyᴹ to *ᴹ
--------------------------------------------------------------------------------

Ty*ᴹ : ∀ {Γ'}(A : Ty Γ') → ∀ {Δ' σ'} (σ'ᴹ : Con'ᴹ Γ' {Δ'} σ') → *ᴹ (Tyₛ σ' A)
Ty*ᴹ {Γ'} A {Δ'} {σ'} σ'ᴹ = con obj' morph' module Ty*ᴹ where
  obj' : *ᴹobjT (Tyₛ σ' A)
  obj' Δ' Δ δ' = let con s p = Tyᴹ A Δ _ (Con'ᴹₑ δ' σ'ᴹ) in con s (coe E p)
    module obj' where abstract E = (λ x → QU Δ x (Tyᴹ A Δ _ (Con'ᴹₑ δ' σ'ᴹ) .S)) & (Ty-ₛ∘ₑ σ' δ' A ⁻¹)

  morph' : *ᴹmorphT obj'
  morph' {Δ'}{Δ}{δ'}{Σ'} Σ ν' ν x = coe E (Tyᴹₑ A (Con'ᴹₑ δ' σ'ᴹ) ν x)
    module morph' where abstract E = ap2 (λ x y → Tyᴹ A Σ x y .S) (ass'ₛₑₑ σ' δ' ν') (Con'ᴹ-∘ₑ δ' ν' σ'ᴹ ⁻¹̃)

abstract
  Ty*ᴹvz :
    ∀ {Γ' Δ' σ' A}(σ'ᴹ : Con'ᴹ Γ' {Δ'} σ') (Aᴹ : *ᴹ A)  → Ty*ᴹ (var vz) (σ'ᴹ , Aᴹ) ≡ Aᴹ
  Ty*ᴹvz {Γ'} {Δ'} {σ'} {A} σ'ᴹ Aᴹ =
    ap2 *ᴹ.con
      (ext λ Σ' → ext λ Σ → ext λ δ' →
        ap2 Cand.con
          ((S ∘ obj Aᴹ Σ' Σ) & idr'ₑ δ')
          (   uncoe (Ty*ᴹ.obj'.E _ _ _ _ _) _
            ◾̃ uncoe (*∈ᴹ.E _ _ _ _ _) _
            ◾̃ uncoe (*ᴹₑ.obj'.E _ _ _ _ _ _) _
            ◾̃ ap̃ (P ∘ obj Aᴹ Σ' Σ) (idr'ₑ δ')))
      (extĩ λ Σ' → extĩ λ Σ → extĩ λ ν' → extĩ λ Ξ' →
       ext̃ λ Ξ → ext̃ λ ε' → ext̃ λ ε →
       ext̃' ((S ∘ obj Aᴹ Σ' Σ) & idr'ₑ ν') (λ x₀ x₁ x₂ →
          uncoe (Ty*ᴹ.morph'.E _ _ _ _ _ _) _
        ◾̃ uncoe (*∈ᴹₑ.E _ _ _ _ _ _) _
        ◾̃ uncoe (*ᴹₑ.morph'.E _ _ _ _ _ _ _) _
        ◾̃ ap2̃ (λ σ' → morph Aᴹ {σ' = σ'} Ξ ε' ε) (idr'ₑ ν') x₂))

  Ty*ᴹ-nat :
    ∀ {Γ' Δ' Σ' σ'}
      (A : Ty Γ') (δ' : OPE' Σ' Δ') (σ'ᴹ : Con'ᴹ Γ' σ')
    → Ty*ᴹ A (Con'ᴹₑ δ' σ'ᴹ) ≅ *ᴹₑ δ' (Ty*ᴹ A σ'ᴹ)
  Ty*ᴹ-nat {Γ'} {Δ'} {Σ'} {σ'} A δ' σ'ᴹ =
    let E1 = Ty-ₛ∘ₑ σ' δ' A ⁻¹ in
    ap3̃ (λ A → *ᴹ.con {A = A}) E1
      (ext̃ λ Ξ' → ext̃ λ Ξ → ext̃ λ ν' →
        let E2 = ass'ₛₑₑ σ' δ' ν'; E3 = Con'ᴹ-∘ₑ δ' ν' σ'ᴹ ⁻¹̃ in
        ap3̃ (λ A → Cand.con {A = Tyₑ ν' A}) E1
          (ap2̃ (λ σ' → S {A = Tyₛ σ' A}) E2
             (ap2̃ (Tyᴹ A Ξ) E2 E3))
          (  uncoe (Ty*ᴹ.obj'.E _ _ _ _ _) _
           ◾̃ ap2̃ (λ x y → P (Tyᴹ A Ξ x y)) E2 E3
           ◾̃ uncoe (Ty*ᴹ.obj'.E _ _ _ _ _) _ ⁻¹̃
           ◾̃ uncoe (*ᴹₑ.obj'.E _ _ _ _ _ _) _ ⁻¹̃))
      (extĩ λ Ξ' → extĩ λ Ξ → extĩ λ ν' → extĩ λ Ω' →
         ext̃ λ Ω → ext̃ λ ε' → ext̃ λ ε →
           let E1 = ass'ₛₑₑ σ' δ' ν'; E2 = Con'ᴹ-∘ₑ δ' ν' σ'ᴹ ⁻¹̃ in
           ext̃'
             (ap2 (λ x y → S (Tyᴹ A Ξ x y)) E1 E2)
             (λ a₀ a₁ a₂ →
                 uncoe (Ty*ᴹ.morph'.E _ _ _ _ _ _) _
               ◾̃ ap3̃ (λ σ' x y → Tyᴹₑ A {σ' = σ'} x ε y) E1 E2 a₂
               ◾̃ uncoe (Ty*ᴹ.morph'.E _ _ _ _ _ _) _ ⁻¹̃
               ◾̃ uncoe (*ᴹₑ.morph'.E _ _ _ _ _ _ _) _ ⁻¹̃))

  Tyₑ*ᴹ :
    ∀ {Γ' Δ' Σ'} (σ' : OPE' Γ' Σ'){δ' : Sub' Δ' Γ'} A (δ'ᴹ : Con'ᴹ Γ' δ')
    → Ty*ᴹ (Tyₑ σ' A) δ'ᴹ ≅ Ty*ᴹ A (OPE'ᴹ σ' δ'ᴹ)
  Tyₑ*ᴹ {Γ'}{Δ'}{Σ'} σ' {δ'} A δ'ᴹ =

    let E1 = λ {Ξ'} (ν' : OPE' Ξ' Δ') →
                (Ty-ₛ∘ₑ δ' ν' (Tyₑ σ' A) ⁻¹
               ◾ Tyₑ ν' & Ty-ₑ∘ₛ σ' δ' A
               ◾ Ty-ₛ∘ₑ (σ' ₑ∘'ₛ δ') ν' A)
               ◾ (λ x → Tyₛ x A) & ass'ₑₛₑ σ' δ' ν' in

    ap3̃ (λ A → *ᴹ.con {A = A})
      (Ty-ₑ∘ₛ σ' δ' A)
      (ext̃ λ Ξ' → ext̃ λ Ξ → ext̃ λ ν' →

       let Hyp = Tyₑᴹ A Ξ σ' (Con'ᴹₑ ν' δ'ᴹ)
           E2  = ass'ₑₛₑ σ' δ' ν' ⁻¹
           E3  = OPE'ᴹ-nat σ' ν' δ'ᴹ in

       ap3̃ (λ A → Cand.con {A = Tyₑ ν' A})
          (Ty-ₑ∘ₛ σ' δ' A)
          (ap2̃ (λ A → S {A = A})
              (E1 ν')
              (   Hyp)
                ◾̃ ap2̃ (λ x y → S (Tyᴹ A Ξ x y)) E2 E3)
          (   uncoe (Ty*ᴹ.obj'.E _ _ _ _ _) _
            ◾̃ (ap2̃ (λ A → P {A = A})
                (E1 ν')
                (  Hyp)
                 ◾̃ ap2̃ (λ x y → P (Tyᴹ A Ξ x y)) E2 E3)
            ◾̃ uncoe (Ty*ᴹ.obj'.E _ _ _ _ _) _ ⁻¹̃))

      (extĩ λ Ξ' → extĩ λ Ξ → extĩ λ ν' → extĩ λ Ω' →
       ext̃ λ Ω → ext̃ λ ε' → ext̃ λ ε →
       ext̃'
         (ap2 (λ A → S {A = A})
           (E1 ν' ◾ (λ x → Tyₛ x A) & (ass'ₑₛₑ σ' δ' ν' ⁻¹))
           (   Tyₑᴹ A Ξ σ' (Con'ᴹₑ ν' δ'ᴹ)
             ◾̃ ap2̃ (Tyᴹ A Ξ) (ass'ₑₛₑ σ' δ' ν' ⁻¹) (OPE'ᴹ-nat σ' ν' δ'ᴹ)))
         (λ x₀ x₁ x₂ →
             uncoe (Ty*ᴹ.morph'.E _ _ _ _ _ _) _
           ◾̃ Tyᴹₑ-shuffle σ' A ν' δ'ᴹ ε x₀ x₁ x₂
           ◾̃ uncoe (Ty*ᴹ.morph'.E _ _ _ _ _ _) _ ⁻¹̃))

-- Substitutions
--------------------------------------------------------------------------------

Sub'ᴹ : ∀ {Γ' Δ'}(σ' : Sub' Γ' Δ') → ∀ {Σ' δ'} → Con'ᴹ Γ' {Σ'} δ' → Con'ᴹ Δ' {Σ'} (σ' ∘'ₛ δ')
Sub'ᴹ ∙        δ'ᴹ = ∙
Sub'ᴹ (σ' , A) δ'ᴹ = Sub'ᴹ σ' δ'ᴹ , Ty*ᴹ A δ'ᴹ

Sub'ᴹ-ₛ∘ₑ :
  ∀ {Γ' Δ' Σ' Ξ'}(σ' : Sub' Σ' Ξ')(δ' : OPE' Γ' Σ'){ν' : Sub' Δ' Γ'}(ν'ᴹ : Con'ᴹ Γ' ν')
  → Sub'ᴹ (σ' ₛ∘'ₑ δ') ν'ᴹ ≅ Sub'ᴹ σ' (OPE'ᴹ δ' ν'ᴹ)
Sub'ᴹ-ₛ∘ₑ ∙        δ' {ν'} ν'ᴹ = refl̃
Sub'ᴹ-ₛ∘ₑ (σ' , A) δ' {ν'} ν'ᴹ =
  ap4̃ (λ σ'' A → Con'ᴹ._,_ {σ' = σ''} {A = A})
    (ass'ₛₑₛ σ' δ' ν')
    (Ty-ₑ∘ₛ δ' ν' A ~)
    (Sub'ᴹ-ₛ∘ₑ σ' δ' ν'ᴹ)
    (Tyₑ*ᴹ δ' A ν'ᴹ)

Sub'ᴹ-nat :
  ∀ {Γ' Δ' Σ' Ξ' σ'} (δ' : Sub' Δ' Γ') (ν' : OPE' Ξ' Σ') (σ'ᴹ : Con'ᴹ Δ' σ')
  → Sub'ᴹ δ' (Con'ᴹₑ ν' σ'ᴹ) ≅ Con'ᴹₑ ν' (Sub'ᴹ δ' σ'ᴹ)
Sub'ᴹ-nat ∙        ν' σ'ᴹ = refl̃
Sub'ᴹ-nat {σ' = σ'} (δ' , A) ν' σ'ᴹ =
  ap4̃ (λ σ' A → Con'ᴹ._,_ {σ' = σ'} {A = A})
    (ass'ₛₛₑ δ' σ' ν' ⁻¹)
    (Ty-ₛ∘ₑ σ' ν' A ⁻¹ ~)
    (Sub'ᴹ-nat δ' ν' σ'ᴹ)
    (Ty*ᴹ-nat A ν' σ'ᴹ)

Sub'ᴹ-id : ∀ {Γ' Δ' σ'}(σ'ᴹ : Con'ᴹ Γ' {Δ'} σ') → Sub'ᴹ id'ₛ σ'ᴹ ≅ σ'ᴹ
Sub'ᴹ-id ∙          = refl̃
Sub'ᴹ-id (_,_ {σ' = σ'} {A} σ'ᴹ Aᴹ) =
  ap3̃ (λ σ' x y → Con'ᴹ._,_ {σ' = σ'} x y)
   (ass'ₛₑₛ id'ₛ wk' (σ' , A) ◾ idl'ₛ (id'ₑ ₑ∘'ₛ σ') ◾ idl'ₑₛ σ')
   (Sub'ᴹ-ₛ∘ₑ id'ₛ wk' (σ'ᴹ , Aᴹ) ◾̃ Sub'ᴹ-id (OPE'ᴹ id'ₑ σ'ᴹ) ◾̃ OPE'ᴹ-id σ'ᴹ)
   (Ty*ᴹvz σ'ᴹ Aᴹ ~)

*∈ₛᴹ :
  ∀ {Γ'} v {Δ' Σ'} Σ δ' {σ'} σ'ᴹ
  → Tyᴹ {Δ'} (*∈ₛ {Γ'} δ' v) {Σ'} Σ σ' σ'ᴹ .S ≡ *∈ᴹ v Σ (δ' ∘'ₛ σ') (Sub'ᴹ δ' σ'ᴹ) .S
*∈ₛᴹ vz {Σ' = Σ'} Σ (δ' , A) {σ'} σ'ᴹ =
   ap2 (λ x y → Tyᴹ A Σ x y .S)
     (idr'ₛₑ σ' ⁻¹)
     (Con'ᴹ-idₑ σ'ᴹ ⁻¹̃)
*∈ₛᴹ (vs v) Σ (δ' , A) σ'ᴹ = *∈ₛᴹ v Σ δ' σ'ᴹ

Tyₛᴹ :
  ∀ {Γ'} A {Δ' Σ'} Σ δ' {σ'} σ'ᴹ
  → Tyᴹ {Δ'} (Tyₛ {Γ'} δ' A) {Σ'} Σ σ' σ'ᴹ .S ≡ Tyᴹ A Σ (δ' ∘'ₛ σ') (Sub'ᴹ δ' σ'ᴹ) .S
Tyₛᴹ (var v) Σ δ' σ'ᴹ = *∈ₛᴹ v Σ δ' σ'ᴹ
Tyₛᴹ (A ⇒ B) Σ δ' {σ'} σ'ᴹ =
  Πi-≡ λ Ξ' → Πi-≡ λ Ξ → Πi-≡ λ ν' → Π-≡ λ ν →
    (λ x y → x → y)
      & (Tyₛᴹ A Ξ δ' (Con'ᴹₑ ν' σ'ᴹ)
        ◾ ap2 (λ x y → Tyᴹ A Ξ x y .S)
            (ass'ₛₛₑ δ' σ' ν' ⁻¹)
            (Sub'ᴹ-nat δ' ν' σ'ᴹ))
      ⊗ (Tyₛᴹ B Ξ δ' (Con'ᴹₑ ν' σ'ᴹ)
        ◾ ap2 (λ x y → Tyᴹ B Ξ x y .S)
            (ass'ₛₛₑ δ' σ' ν' ⁻¹)
            (Sub'ᴹ-nat δ' ν' σ'ᴹ))
Tyₛᴹ {Γ'} (∀' A) Σ δ' {σ'} σ'ᴹ =
  Πi-≡ λ Ξ' → Πi-≡ λ Ξ → Πi-≡ λ ν' → Π-≡ λ ν → Π-≡ λ B → Π-≡ λ Bᴹ →
    Tyₛᴹ A Ξ (keep'ₛ δ') (Con'ᴹₑ ν' σ'ᴹ , Bᴹ)
    ◾ ap3 (λ σ' σ'ᴹ Bᴹ → Tyᴹ A Ξ (σ' , B) (σ'ᴹ , Bᴹ) .S)
        (   ass'ₛₑₛ δ' wk' (σ' ₛ∘'ₑ ν' , B)
          ◾ (δ' ∘'ₛ_) & idl'ₑₛ (σ' ₛ∘'ₑ ν')
          ◾ ass'ₛₛₑ δ' σ' ν' ⁻¹)
        (   Sub'ᴹ-ₛ∘ₑ δ' wk' (Con'ᴹₑ ν' σ'ᴹ , Bᴹ)
          ◾̃ ap2̃ (λ x → Sub'ᴹ δ' {δ' = x})
              (idl'ₑₛ (σ' ₛ∘'ₑ ν'))
              (OPE'ᴹ-id (Con'ᴹₑ ν' σ'ᴹ))
          ◾̃ Sub'ᴹ-nat δ' ν' σ'ᴹ)
        (Ty*ᴹvz (Con'ᴹₑ ν' σ'ᴹ) Bᴹ ~)

