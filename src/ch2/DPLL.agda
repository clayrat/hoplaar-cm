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
open import FMap
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

-- iterative

data Trailmix : 𝒰 where
  guessed deduced : Trailmix

Trail : 𝒰 → 𝒰
Trail A = List (Lit A × Trailmix)

backtrack : Trail A → Trail A
backtrack   []                   = []
backtrack   ((_ , deduced) ∷ xs) = backtrack xs
backtrack t@((p , guessed) ∷ xs) = t

unassigned : ⦃ d : is-discrete A ⦄
           → CNF A → Trail A → List (Lit A)
unassigned cls trail =
  subtract
    (unions (image (image abs) cls))
    (image (abs ∘ fst) trail)

-- TODO use ListSet instead of FMap Lit ⊤
{-# TERMINATING #-}
unit-subpropagate-iter : ⦃ d : is-discrete A ⦄
                       → CNF A → FMap (Lit A) ⊤ → Trail A
                       → CNF A × FMap (Lit A) ⊤ × Trail A
unit-subpropagate-iter cls fn tr =
  let cls' = map (filter (not ∘ defined fn ∘ negate)) cls
      newunits = unions (filter (λ where
                                     [] → false
                                     (x ∷ []) → not (defined fn x)
                                     (_ ∷ _ ∷ _) → false)
                                 cls')
    in
  if is-nil? newunits
     then cls' , fn , tr
          -- why not just map (_, deduced) newunits ++ tr ?
     else let tr' = List.rec tr (λ p → (p , deduced) ∷_) newunits
              fn' = List.rec fn (λ u → upd u tt) newunits
            in
          unit-subpropagate-iter cls' fn' tr'

unit-propagate-iter : ⦃ d : is-discrete A ⦄
                    → CNF A → Trail A
                    → CNF A × Trail A
unit-propagate-iter cls tr =
  let fn = List.rec emp (λ x → upd (x .fst) tt) tr
      (cls' , fn' , tr') = unit-subpropagate-iter cls fn tr
    in
  cls' , tr'

{-# TERMINATING #-}
dpli : ⦃ d : is-discrete A ⦄
     → CNF A → Trail A → Bool
dpli cls tr =
  let (cls' , tr') = unit-propagate-iter cls tr in
  if List.has [] cls'
     then Maybe.rec false (λ where
                               ((p , guessed) , trr) →
                                   dpli cls ((negate p , deduced) ∷ trr)
                               ((_ , deduced) , _)   → false   -- impossible
                          ) (unconsᵐ (backtrack tr))
     else
       let ps = unassigned cls tr' in
       if is-nil? ps
         then true
         else let lcounts = map (posneg-count cls') ps in
              Maybe.rec true -- unreachable
                (λ p → dpli cls ((p , guessed) ∷ tr')) $
                map (snd ∘ foldr₁ (max-on fst)) $
                from-list lcounts

dplisat : Form → Bool
dplisat fm = dpli (defcnfs fm) []

dplitaut : Form → Bool
dplitaut = not ∘ dplisat ∘ Not

main : Main
main =
  run $
  do put-str-ln $ "prime (DPLL) 17: " ++ₛ (show $ dplltaut $ prime 17)
     put-str-ln $ "prime (DPLI) 17: " ++ₛ (show $ dplitaut $ prime 17)

