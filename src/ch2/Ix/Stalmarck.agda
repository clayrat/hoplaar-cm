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
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.All renaming (All to Allₘ)
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
  if enegative? p
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

-- TODO move to KVMapU
lookupm∈ : {K V : 𝒰} ⦃ d : is-discrete K ⦄
         → (m : KVMap K V) (k : K)
         → k ∈ keysm m
         → V
lookupm∈ {V} m a a∈ =
  Maybe.elim
    (λ q → lookupm m a ＝ q → V)
    (λ n → absurd (lookup→∉ (m .inv) n a∈))
    (λ x _ → x)
    (lookupm m a) refl

esubst : {Γ Δ : Ctx}
       → (m : KVMap Var (ELit Δ))
       → (l : ELit Γ)
       → Allₘ (_∈ keysm m) (unevar l)
       → ELit Δ
esubst sub (elit (Pos l)) (just p) = lookupm∈ sub (unvar l) p
esubst sub (elit (Neg l)) (just p) = enegate (lookupm∈ sub (unvar l) p)
esubst sub  etrue          _       = etrue
esubst sub  efalse         _       = efalse

pqrlist : List Var
pqrlist = "p" ∷ "q" ∷ "r" ∷ []

pqr : Ctx
pqr = from-list pqrlist

inst-trigger : AVar Γ × ELit Γ × ELit Γ → List (Trigger pqr) → List (Trigger Γ)
inst-trigger {Γ} = map ∘ instnfn
  where
  aux : (e : ELit pqr) → Allₘ (_∈ pqrlist) (unevar e)
  aux (elit x) = just (list-⊆ (unlit∈ x))
  aux  etrue   = nothing
  aux  efalse  = nothing
  instfn : AVar Γ × ELit Γ × ELit Γ → ELit pqr → ELit Γ
  instfn (x , y , z) e =
    let sub : KVMap Var (ELit Γ)
        sub = insertm "r" z $
              insertm "q" y $
              insertm "p" (elit $ Pos x) $
              emptym
      in
    esubst sub e (aux e)
  inst2fn : AVar Γ × ELit Γ × ELit Γ → Eqv pqr → Eqv Γ
  inst2fn i (p , q) = align (instfn i p , instfn i q)
  instnfn : AVar Γ × ELit Γ × ELit Γ → Trigger pqr → Trigger Γ
  instnfn i (a , c) = inst2fn i a , map (inst2fn i) c

trigger' : ({Γ : Ctx} → Formulaᵢ Γ → Formulaᵢ Γ → Formulaᵢ Γ)
         → List (Trigger pqr)
trigger' op = triggers $ Iff (Atom p') (op (Atom q') (Atom r'))
  where
  p' : AVar pqr
  p' = av "p" (hereₛ refl)
  q' : AVar pqr
  q' = av "q" (thereₛ $ hereₛ refl)
  r' : AVar pqr
  r' = av "r" (thereₛ $ thereₛ $ hereₛ refl)

trigger : Triplet Γ → List (Trigger Γ)
trigger (x , duand y z) = inst-trigger (x , y , z) $ trigger' And
trigger (x , duor  y z) = inst-trigger (x , y , z) $ trigger' Or
trigger (x , duiff y z) = inst-trigger (x , y , z) $ trigger' Iff

-- 0-saturation

ListMap : 𝒰 → 𝒰 → 𝒰
ListMap K V = KVMap K (List V)

look : {K V : 𝒰} ⦃ d : is-discrete K ⦄ → ListMap K V → K → List V
look m l = Maybe.rec [] id (lookupm m l)

TrigMap : LFSet A → 𝒰
TrigMap Γ = ListMap (ELit Γ) (Trigger Γ)

relevance : List (Trigger Γ) → TrigMap Γ
relevance {Γ} trigs =
  List.rec (the (TrigMap Γ) emptym) insert-relevant2 trigs
  where
  insert-relevant : ELit Γ → Trigger Γ → TrigMap Γ → TrigMap Γ
  insert-relevant p trg f =
    insertm p (insert-s trg (look f p)) f
  insert-relevant2 : Trigger Γ → TrigMap Γ → TrigMap Γ
  insert-relevant2 trg@((p , q) , _) =
    insert-relevant p trg ∘ insert-relevant q trg

Erf : ⦃ d : is-discrete A ⦄ → LFSet A → 𝒰
Erf Γ = EClass Γ × TrigMap Γ

equatecons : Eqv Γ → Erf Γ → List (Eqv Γ) × Erf Γ
equatecons (p0 , q0) erf@(eqv , rfn) =
  let p = canonize eqv p0
      q = canonize eqv q0
    in
  if p =? q
    then [] , erf
    else
      let p' = canonize eqv (enegate p0)
          q' = canonize eqv (enegate q0)
          eqv' = equate2 (p , q) eqv
          sp-pos = look rfn p
          sp-neg = look rfn p'
          sq-pos = look rfn q
          sq-neg = look rfn q'
          rfn' = insertm (canonize eqv' p)  (union sp-pos sq-pos) $
                 insertm (canonize eqv' p') (union sp-neg sq-neg) rfn
          nw = union (intersect sp-pos sq-pos) (intersect sp-neg sq-neg)
        in
      (List.rec [] (union ∘ snd) nw) , (eqv' , rfn')
