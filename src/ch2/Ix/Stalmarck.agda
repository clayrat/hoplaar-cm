module ch2.Ix.Stalmarck where

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
open import Data.Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.List.Operations.Discrete
open import Data.String

open import Order.Diagram.Meet
open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open import Order.Constructions.String
import Order.Diagram.Join.Reasoning as JR
open decminmax ℕ-dec-total
open JR ℕₚ max-joins

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Induction.Nat.Strong as Box using (□_)

open import KVListU
open import KVMapU

open import ListSet
open import UnionFindT
open import ch2.Formula
open import ch2.Ix.Formula
open import ch2.Ix.Sem
open import ch2.Ix.Lit
open import ch2.Ix.NF
open import ch2.Ix.CNF
-- open import ch2.Appl

private variable
  A B : 𝒰
  Γ Δ : Ctx

open KVListU.Ops
open KVOps
open KVOps2
open KVProp

-- equational classes

EClass : ⦃ d : is-discrete A ⦄ → LFSet A → 𝒰
EClass Γ = Partition (ELit Γ)

ec-nonterminals≤ : ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
                 → {ec : EClass Γ}
                 → nonterminals ec ≤ 2 + 2 · sizeₛ Γ
ec-nonterminals≤ {Γ} {ec} =
    nonterm≤ {p = ec}
  ∙ =→≤ (size-unique (ec .pg .inv) ⁻¹)
  ∙ elit-set-size {l = from-list (equated ec)}

ecpartitions : ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
             → EClass Γ → ℕ
ecpartitions {Γ} ec =
  2 + 2 · sizeₛ Γ ∸ nonterminals ec

equate-ecpartitions : ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
                    → {ec : EClass Γ} {a b : ELit Γ}
                    → ⌞ not (equivalent ec a b) ⌟
                    → ecpartitions (equate a b ec) < ecpartitions ec
equate-ecpartitions {Γ} {ec} {a} {b} neq =
  <-∸-2l-≃ {m = 2 + 2 · sizeₛ Γ}
           {n = nonterminals (equate a b ec)}
           {p = nonterminals ec}
    (ec-nonterminals≤ {ec = equate a b ec}) ⁻¹ $
  (equate-nonterminals {p = ec} neq)

-- triplication

triplicate : Formulaᵢ Γ → Σ[ Δ ꞉ Ctx ] (ELit (Δ ∪∷ Γ) × List (Triplet (Δ ∪∷ Γ)))
triplicate {Γ} fm =
  let fm' = the (NENF Γ) (nenf0 fm)
      n = suc (over-varsᵢ (max-var-ix "p_") (nenf→formᵢ fm') 0)
      (Δ , l , defs , _) = maincnf {Γ = Γ} fm' emptym n
    in
  Δ , l , valsm defs

-- equivalences

Eqv : LFSet A → 𝒰
Eqv Γ = ELit Γ × ELit Γ

instance
  Show-eqv : {Γ : LFSet A} → ⦃ s : Show A ⦄ → Show (Eqv Γ)
  Show-eqv = default-show λ where
                              (p , q) → show p ++ₛ "<=>" ++ₛ show q

-- simple rules

align-pol : Eqv Γ → Eqv Γ
align-pol (p , q) =
  if enegative p
    then enegate p , enegate q
    else p , q

align : Eqv Γ → Eqv Γ
align (p , q) =
  if elit-< _<str?_ (eabs p) (eabs q)
    then align-pol (q , p)
    else align-pol (p , q)

equate2 : ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
        → Eqv Γ → EClass Γ → EClass Γ
equate2 (p , q) = equate (enegate p) (enegate q) ∘ equate p q

irredundant : ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
            → EClass Γ → List (Eqv Γ) → List (Eqv Γ)
irredundant rel []              = []
irredundant rel ((p , q) ∷ eqs) =
  if equivalent rel p q
    then irredundant rel eqs
    else insert-s (p , q) (irredundant (equate2 (p , q) rel) eqs)

consequences : ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
             → Eqv Γ → Formulaᵢ Γ
             → List (Eqv Γ) → List (Eqv Γ)
consequences {A} {Γ} (p , q) fm eqs =
  irredundant (equate2 (p , q) unequal) (filter follows eqs)
  where
  follows : ELit Γ × ELit Γ → Bool
  follows (r , s) =
    tautology $
    Imp (And (Iff (elit→form p) (elit→form q)) fm)
        (Iff (elit→form r) (elit→form s))

Trigger : LFSet A → 𝒰
Trigger Γ = Eqv Γ × List (Eqv Γ)

instance
  Show-trigger : {Γ : LFSet A} → ⦃ s : Show A ⦄ → Show (Trigger Γ)
  Show-trigger =
    default-show $
    λ where
        (pq , eqs) → "eqv: " ++ₛ show ⦃ r = Show-eqv ⦄ pq ++ₛ "\n" ++ₛ
                     "csq: " ++ₛ show ⦃ r = Show-List ⦃ Show-eqv ⦄ ⦄ eqs ++ₛ "\n"

alignedeqs : Formulaᵢ Γ → List (Eqv Γ)
alignedeqs fm =
  let poslits = insert-s etrue (map (elit ∘ Pos) (atomsᵢ fm))
      lits = union poslits (map enegate poslits)
      pairs = map² _,_ lits lits
      npairs = filter (λ (p , q) → not (eabs p =? eabs q)) pairs
   in
  setify (map align npairs)

triggers : Formulaᵢ Γ → List (Trigger Γ)
triggers fm =
  let eqs = alignedeqs fm
      raw = map (λ pq → pq , consequences pq fm eqs) eqs
    in
  filter (is-cons? ∘ snd) raw
