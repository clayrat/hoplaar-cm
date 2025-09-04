{-# OPTIONS --no-exact-split #-}
module ch2.DPLL where

open import Foundations.Prelude
open import Meta.Show
open import Meta.Effect hiding (_>>_) renaming (_>>=_ to _>>=ᵐ_)
open import Meta.Effect.Bind.State
open import Logic.Discreteness
open import System.Everything hiding (_<$>_)

open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.List.Operations.Discrete
open import Data.String

open import Order.Diagram.Meet
open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open decminmax ℕ-dec-total

open import Data.List.NonEmpty as List⁺

open import ListSet
open import ch2.Formula
open import ch2.Sem
open import ch2.NF
open import ch2.Appl
open import ch2.CNF
open import ch2.DP

private variable
  A : 𝒰

posneg-count : ⦃ d : is-discrete A ⦄
             → CNF A → Lit A → ℕ × Lit A
posneg-count cls l =
  let m = length $ filter (List.has          l) cls
      n = length $ filter (List.has $ negate l) cls in
  m + n , l

{-# TERMINATING #-}
dpll : ⦃ d : is-discrete A ⦄
     → CNF A → Bool
dpll         []      = true
dpll clauses@(_ ∷ _) =
  if List.has [] clauses
    then false
    else Maybe.rec (Maybe.rec
                      (let pvs = filter positive (unions clauses)
                           lcounts = map (posneg-count clauses) pvs
                        in
                       Maybe.rec true -- unreachable
                                 (λ p →    dpll (insert-s (p ∷ []) clauses)
                                        or dpll (insert-s (negate p ∷ []) clauses)) $
                       map (snd ∘ foldr₁ (max-on fst)) $
                       from-list lcounts)
                       dpll
                       (affirmative-negative-rule clauses))
                   dpll
                   (one-lit-rule clauses)

dpllsat : Form → Bool
dpllsat = dpll ∘ defcnfs

dplltaut : Form → Bool
dplltaut = not ∘ dpllsat ∘ Not

main : Main
main =
  run $
  do -- put-str-ln $ "prime        11: " ++ₛ (show $ tautology $ prime 11)
     put-str-ln $ "prime (DPLL) 131: " ++ₛ (show $ dplltaut  $ prime 131)


