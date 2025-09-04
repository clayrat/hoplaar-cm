{-# OPTIONS --safe #-}
module ListSet where

open import Foundations.Prelude
open import Meta.Effect
open import Logic.Discreteness
open import Functions.Embedding

open import Data.Reflects
open import Data.Dec
open import Data.Nat.Properties
open import Data.List as List
open import Data.List.Operations.Properties
open import Data.List.Operations.Rel
open import Data.List.Operations.Discrete
open import Data.List.Correspondences.Binary.OPE

private variable
  A B : 𝒰

union : ⦃ d : is-discrete A ⦄
       → List A → List A → List A
union xs ys = nub _=?_ $ xs ++ ys

union-empty : ⦃ d : is-discrete A ⦄
            → {xs ys : List A}
            → union xs ys ＝ []
            → (xs ＝ []) × (ys ＝ [])
union-empty {xs} {ys} p =
 let (xl , yl) = +=0-2 (length xs) (length ys)
                       (  ++-length xs ys ⁻¹
                        ∙ ap length (nub-[] {xs = xs ++ ys} p))
   in
 length=0→nil xl , length=0→nil yl

insert-s : ⦃ d : is-discrete A ⦄
         → A → List A → List A
insert-s x xs = nub _=?_ $ x ∷ xs

unions : ⦃ d : is-discrete A ⦄
       → List (List A) → List A
unions = nub _=?_ ∘ concat

image : ⦃ d : is-discrete B ⦄
      → (A → B) → List A → List B
image f = nub _=?_ ∘ map f

image-empty : ⦃ d : is-discrete B ⦄
            → {f : A → B} {xs : List A}
            → image f xs ＝ []
            → xs ＝ []
image-empty {f} {xs = []}     _ = refl
image-empty {f} {xs = x ∷ xs}   = false!

∈-image : ⦃ d : is-discrete B ⦄
        → {f : A → B} {xs : List A} {x : A}
        → x ∈ xs → f x ∈ image f xs
∈-image ⦃ d ⦄ x∈ = ⊆-nub {R = λ _ _ → d .proof} (∈-map _ x∈)

image-∈ : ⦃ d : is-discrete B ⦄
        → {f : A → B} {xs : List A} {x : A}
        → Injective f
        → f x ∈ image f xs → x ∈ xs
image-∈ finj = map-∈ _ finj ∘ ope→subset nub-ope

