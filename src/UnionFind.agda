module UnionFind where

open import Foundations.Prelude
open import Logic.Discreteness
open import Data.Bool
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.List

open import FMap

private variable
  A : 𝒰

data Pnode (A : 𝒰) : 𝒰 where
  nonterminal : A → Pnode A
  terminal    : A → ℕ → Pnode A

record Partition (A : 𝒰) : 𝒰 where
  constructor mkpartition
  field
    mp : FMap A (Pnode A)

-- TODO termination proof
-- this involves reasoning on the internal map structure (removing traversed keys)
{-# TERMINATING #-}
terminus : Partition A → A → Maybe (A × ℕ)
terminus p@(mkpartition mp) a =
  -- TODO >>=
  Maybe.rec
    nothing
    (λ where
         (nonterminal x) → terminus p x
         (terminal x n) → just (x , n))
    (lup mp a)

try-terminus : Partition A → A → A × ℕ
try-terminus p a =
  Maybe.rec
    (a , 1)
    id
    (terminus p a)

canonize : Partition A → A → A
canonize env = fst ∘ try-terminus env

equivalent : ⦃ d : is-discrete A ⦄
           → Partition A → A → A → Bool
equivalent eqv a b = canonize eqv a =? canonize eqv b

equate : ⦃ d : is-discrete A ⦄
       → A → A → Partition A → Partition A
equate a b p@(mkpartition mp) =
  let (a' , na) = try-terminus p a
      (b' , nb) = try-terminus p b
    in
  mkpartition $
  if a' =? b'
     then mp
     else if na ≤? nb
             then (upd a' (nonterminal b') $
                   upd b' (terminal b' (na + nb)) $
                   mp)
             else (upd b' (nonterminal a') $
                   upd a' (terminal a' (na + nb)) $
                   mp)

unequal : Partition A
unequal = mkpartition emp

equated : Partition A → List A
equated (mkpartition mp) = dom mp
