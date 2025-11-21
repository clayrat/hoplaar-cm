module ch2.Ix.EClass where

open import Prelude hiding (_≠_)
open import Foundations.Sigma
open Variadics _
open import Meta.Effect hiding (_>>_) renaming (_>>=_ to _>>=ᵐ_)
open import Meta.Show
open import Meta.Effect.Bind.State
open import Logic.Discreteness
open import System.Everything hiding (_<$>_)

open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.All renaming (All to Allₘ)
open import Data.List as List
open import Data.List.Operations.Discrete
open import Data.String
open import Data.Sum

open import Order.Constructions.String

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import KVListU
open import KVMapU

open import UnionFindT
open import ch2.Formula
open import ch2.Ix.Formula
open import ch2.Ix.Lit

private 
  variable
    A : 𝒰
    Γ : LFSet A
  
-- equational classes

EClass : {A : 𝒰} → ⦃ d : is-discrete A ⦄
       → LFSet A → 𝒰
EClass Γ = Partition (ELit Γ)

ec-nonterminals≤ : {A : 𝒰} → ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
                 → {ec : EClass Γ}
                 → nonterminals ec ≤ 2 + 2 · sizeₛ Γ
ec-nonterminals≤ {Γ} {ec} =
    nonterm≤ {p = ec}
  ∙ =→≤ (size-unique (ec .pg .inv) ⁻¹)
  ∙ elit-set-size {l = from-list (equated ec)}

ecpartitions : {A : 𝒰} → ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
             → EClass Γ → ℕ
ecpartitions {Γ} ec =
  2 + 2 · sizeₛ Γ ∸ nonterminals ec

opaque
  <-∸-2l-≃' : ∀ {m n p} → n ≤ m → (m ∸ n < m ∸ p) ≃ (p < n)
  <-∸-2l-≃' {m} {n} {p} n≤m =
      <-∸-r-≃ ∙ₑ =→≃ (ap (_< m) (+-comm p _))
    ∙ₑ <-∸-r-≃ ⁻¹ ∙ₑ =→≃ (ap (p <_) (∸∸=id _ _ n≤m))

  ≤-∸-2l-≃' : ∀ {m n p} → p ≤ m → (m ∸ n ≤ m ∸ p) ≃ (p ≤ n)
  ≤-∸-2l-≃' {m} {n} {p} p≤m =
      ≤-∸-l-≃ {m = m} {n = n}
    ∙ₑ =→≃ (ap (_≤ n) (∸∸=id _ _ p≤m))

  equate-ecpartitions-neq : {A : 𝒰} → ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
                          → {ec : EClass Γ} {a b : ELit Γ}
                          → ⌞ not (equivalent ec a b) ⌟
                          → ecpartitions (equate a b ec)
                          < ecpartitions ec
  equate-ecpartitions-neq {Γ} {ec} {a} {b} neq =
    <-∸-2l-≃' {p = nonterminals ec}
      (ec-nonterminals≤ {ec = equate a b ec}) ⁻¹ $
      equate-nonterminals-neq {p = ec} {a = a} {b = b} neq

  equate-ecpartitions : {A : 𝒰} → ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
                      → {ec : EClass Γ} {a b : ELit Γ}
                      → ecpartitions (equate a b ec) ≤ ecpartitions ec
  equate-ecpartitions {ec} {a} {b} =
    ≤-∸-2l-≃' {n = nonterminals (equate a b ec)} (ec-nonterminals≤ {ec = ec}) ⁻¹ $
    equate-nonterminals {p = ec}

-- equivalences

Eqv : LFSet A → 𝒰
Eqv Γ = ELit Γ × ELit Γ

instance
  Show-eqv : {Γ : LFSet A} → ⦃ s : Show A ⦄ → Show (Eqv Γ)
  Show-eqv = default-show λ where
                              (p , q) → show p ++ₛ "<=>" ++ₛ show q

align-pol : Eqv Γ → Eqv Γ
align-pol (p , q) =
  if enegative? p
    then enegate p , enegate q
    else p , q

align : {Γ : Ctx} → Eqv Γ → Eqv Γ
align (p , q) =
  if elit-< _<str?_ (eabs p) (eabs q)
    then align-pol (q , p)
    else align-pol (p , q)

equate2 : ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
        → Eqv Γ → EClass Γ → EClass Γ
equate2 (p , q) = equate (enegate p) (enegate q) ∘ equate p q

equate2-ecpartitions : ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
                     → {ec : EClass Γ} {ab : Eqv Γ}
                     → ⌞ not (equivalent ec (ab .fst) (ab .snd)) ⌟
                     → ecpartitions (equate2 ab ec) < ecpartitions ec
equate2-ecpartitions {Γ} {ec} {ab = (a , b)} neq =
  ≤-<-trans
    (equate-ecpartitions {ec = equate a b ec})
    (equate-ecpartitions-neq {ec = ec} neq)

