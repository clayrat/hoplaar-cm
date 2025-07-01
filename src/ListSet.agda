{-# OPTIONS --safe #-}
module ListSet where

open import Foundations.Prelude
open import Meta.Effect
open import Logic.Discreteness

open import Data.List as List
open import Data.List.Operations.Discrete

private variable
  A B : 𝒰

union : ⦃ d : is-discrete A ⦄
       → List A → List A → List A
union xs ys = nub _=?_ $ xs ++ ys

unions : ⦃ d : is-discrete A ⦄
       → List (List A) → List A
unions = nub _=?_ ∘ concat

image : ⦃ d : is-discrete B ⦄
      → (A → B) → List A → List B
image f = nub _=?_ ∘ map f
