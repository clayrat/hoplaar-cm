module UnionFind where

open import Prelude
open import Foundations.Sigma
open import Logic.Discreteness
open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.List

-- open import FMap

open import KVListU
open import KVMapU

private variable
  A : 𝒰

open KVListU.Ops
open KVOps
open KVOps2

data Pnode (A : 𝒰) : 𝒰 where
  nonterminal : A → Pnode A
  terminal    : A → ℕ → Pnode A

nodeval : Pnode A → A
nodeval (nonterminal a) = a
nodeval (terminal a _)  = a

noderank : Pnode A → Maybe ℕ
noderank (nonterminal _) = nothing
noderank (terminal _ n)  = just n

is-nonterminal : Pnode A → 𝒰
is-nonterminal (nonterminal _) = ⊤
is-nonterminal (terminal _ _) = ⊥

nonterminal≠terminal : {a b : A} {k : ℕ}
                     → nonterminal a ≠ terminal b k
nonterminal≠terminal p = subst is-nonterminal p tt

nonterminal-inj : {a b : A}
                → nonterminal a ＝ nonterminal b
                → a ＝ b
nonterminal-inj = ap nodeval

terminal-inj : {a b : A} {n m : ℕ}
             → terminal a n ＝ terminal b m
             → (a ＝ b) × (n ＝ m)
terminal-inj e = ap nodeval e , ap (Maybe.rec 0 id ∘ noderank) e

Pnode-= : (A → A → Bool) → Pnode A → Pnode A → Bool
Pnode-= eq (nonterminal x) (nonterminal y) = eq x y
Pnode-= eq (terminal x n)  (terminal y m)  = eq x y and (n == m)
Pnode-= _ _ _ = false

Reflects-Pnode-= : {eq : A → A → Bool}
                   ⦃ r : ∀ {x y} → Reflects (x ＝ y) (eq x y) ⦄
                 → ∀ {x y} → Reflects (x ＝ y) (Pnode-= eq x y)
Reflects-Pnode-= ⦃ r ⦄ {x = nonterminal x} {y = nonterminal y} =
  Reflects.dmap
    (ap nonterminal)
    (contra nonterminal-inj)
    (r {x = x})
Reflects-Pnode-=       {x = nonterminal x} {y = terminal y m}  =
  ofⁿ nonterminal≠terminal
Reflects-Pnode-=       {x = terminal x n}  {y = nonterminal y} =
  ofⁿ (nonterminal≠terminal ∘ _⁻¹)
Reflects-Pnode-= ⦃ r ⦄ {x = terminal x n}  {y = terminal y m}  =
  Reflects.dmap
    ((λ e1 → ap² terminal e1) $²_)
    (contra terminal-inj)
    (Reflects-× ⦃ rp = r {x = x} ⦄ ⦃ rq = Reflects-ℕ-Path {m = n} ⦄ )

instance
  Pnode-discrete : ⦃ d : is-discrete A ⦄
                 → is-discrete (Pnode A)
  Pnode-discrete ⦃ d ⦄ {x} {y} .does = Pnode-= (λ x y → d {x = x} {y = y} .does) x y
  Pnode-discrete .proof = Reflects-Pnode-=

record Partition (A : 𝒰) : 𝒰 where
  constructor mkpartition
  field
    mp : KVMap A (Pnode A)

open Partition public

unquoteDecl Partition-iso = declare-record-iso Partition-iso (quote Partition)

instance
  Partition-discrete : ⦃ d : is-discrete A ⦄
                     → is-discrete (Partition A)
  Partition-discrete ⦃ d ⦄ = ≅→is-discrete Partition-iso auto

-- terminating version in UnionFindT
{-# TERMINATING #-}
terminus : ⦃ d : is-discrete A ⦄
         → Partition A → A → Maybe (A × ℕ)
terminus p@(mkpartition mp) a =
  -- TODO >>=
  Maybe.rec
    nothing
    (λ where
         (nonterminal x) → terminus p x
         (terminal x n) → just (x , n))
    (lookupm mp a)

try-terminus : ⦃ d : is-discrete A ⦄
             → Partition A → A → A × ℕ
try-terminus p a =
  Maybe.rec
    (a , 1)
    id
    (terminus p a)

canonize : ⦃ d : is-discrete A ⦄
         → Partition A → A → A
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
             then (insertm a' (nonterminal b') $
                   insertm b' (terminal b' (na + nb)) $
                   mp)
             else (insertm b' (nonterminal a') $
                   insertm a' (terminal a' (na + nb)) $
                   mp)

unequal : ⦃ d : is-discrete A ⦄
        → Partition A
unequal = mkpartition emptym

equated : ⦃ d : is-discrete A ⦄
        → Partition A → List A
equated (mkpartition mp) = keysm mp
