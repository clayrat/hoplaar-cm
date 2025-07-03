{-# OPTIONS --no-exact-split #-}
module ch2.DP where

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

private variable
  A : 𝒰

-- aka BCP aka unit propagation
one-lit-rule : ⦃ d : is-discrete A ⦄
             → CNF A → Maybe (CNF A)
one-lit-rule clauses =
  findᵐ (λ cl → length cl == 1) clauses >>=ᵐ
   λ where
      (u ∷ []) → just $ image (rem $ negate u) $
                        filter (not ∘ List.has u) clauses
      -- impossible
      (_ ∷ _ ∷ _) → nothing
      [] → nothing

-- aka pure literal rule
affirmative-negative-rule : ⦃ d : is-discrete A ⦄
                          → CNF A → Maybe (CNF A)
affirmative-negative-rule clauses =
  let (neg0 , pos) = partition negative (unions clauses)
      neg = image negate neg0
      posonly = diff pos neg
      negonly = diff neg pos
      pr = union posonly (image negate negonly)
    in
  if is-nil? pr
    then nothing
    else just (filter (is-nil? ∘ intersect pr) clauses)

-- TODO clause thm

resolve-on : ⦃ d : is-discrete A ⦄
           → Lit A → CNF A → CNF A
resolve-on p clauses =
  let p' = negate p
      (pos , notpos) = partition (List.has p) clauses
      (neg , other) = partition (List.has p') notpos
      pos' = image (filter (not ∘ _=? p)) pos
      neg' = image (filter (not ∘ _=? p')) neg
      res0 = map² union pos' neg'
    in
  union other (filter (not ∘ trivial?) res0)

resolution-blowup : ⦃ d : is-discrete A ⦄
                  → CNF A → Lit A → ℕ × Lit A
resolution-blowup cls l =
  let m = length $ filter (List.has          l) cls
      n = length $ filter (List.has $ negate l) cls in
  (m · n ∸ m ∸ n , l)

resolution-rule : ⦃ d : is-discrete A ⦄
                → CNF A → CNF A
resolution-rule clauses =
   let pvs = filter positive (unions clauses)
       lblows = map (resolution-blowup clauses) pvs
     in
   Maybe.rec clauses
             (λ p → resolve-on p clauses) $
   map (snd ∘ foldr₁ (min-on fst)) $
   from-list lblows

{-# TERMINATING #-}
dp : ⦃ d : is-discrete A ⦄
   → CNF A → Bool
dp         []      = true
dp clauses@(_ ∷ _) =
  if List.has [] clauses
    then false
    else Maybe.rec (Maybe.rec (dp (resolution-rule clauses))
                              dp
                              (affirmative-negative-rule clauses))
                   dp
                   (one-lit-rule clauses)

dpsat : Form → Bool
dpsat = dp ∘ defcnfs

dptaut : Form → Bool
dptaut = not ∘ dpsat ∘ Not

main : Main
main =
  run $
  do put-str-ln $ "prime 11  : " ++ₛ (show $ tautology $ prime 11)
     put-str-ln $ "prime 11DP: " ++ₛ (show $ dptaut $ prime 11)

