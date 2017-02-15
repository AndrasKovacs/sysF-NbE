{-# OPTIONS --without-K --type-in-type #-}

module Normalization where

open import Lib
open import Type
open import Term
open import TypeModel
open import TermModel

uCon' : ∀ (Γ' : Con') → Con'ᴹ Γ' {Γ'} id'ₛ
uCon' ∙       = ∙
uCon' (Γ' ,*) = Con'ᴹₑ (drop id'ₑ) (uCon' Γ') , u* vz

uCon : ∀ Γ' Γ → Conᴹ {Γ'} Γ Γ (uCon' Γ')
uCon ∙      ∙       = ∙
uCon Γ'     (Γ , A) =
  coe (ap2 (λ σ' → Conᴹ Γ (Γ , A) {σ'}) (idr'ₛₑ id'ₛ) (Con'ᴹ-idₑ (uCon' Γ')))
    (Conᴹₑ (drop {A = A} idₑ) (uCon Γ' Γ)) ,
  Tyᴹ A (Γ , A) id'ₛ (uCon' Γ') .U (coe (Ne (Γ , A) & (Ty-idₛ A ⁻¹)) (var vz))
uCon (Γ' ,*) (Γ ,*) = Conᴹₑ (drop' idₑ) (uCon Γ' Γ) ,*

nf : ∀ {Γ' A Γ} → Tm {Γ'} Γ A → Nf Γ A
nf {Γ'}{A}{Γ} t = coe (Nf Γ & Ty-idₛ A) (Tyᴹ A Γ _ (uCon' Γ') .Q (Tmᴹ t _ (uCon Γ' Γ)))

