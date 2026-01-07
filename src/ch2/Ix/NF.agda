{-# OPTIONS --no-exact-split #-}
module ch2.Ix.NF where

open import Prelude hiding (_≠_)
open import Meta.Effect hiding (_>>_ ; _>>=_)
open import Meta.Show
open import Logic.Discreteness
open import System.Everything hiding (_<$>_)

open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Char
open import Data.String
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Any renaming (here to hereₘ)
open import Data.List as List
open import Data.List.Operations.Properties
open import Data.List.Operations.Discrete renaming (rem to remₗ)
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Operations.Rel
open import Data.Sum

open import Data.List.NonEmpty as List⁺

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import ListSet
open import ch2.Formula
-- open import ch2.Sem
open import ch2.Ix.Formula
open import ch2.Ix.Sem
open import ch2.Ix.Lit

private variable
  A B : 𝒰
  Γ : LFSet A

psimplify1 : Formulaᵢ Γ → Formulaᵢ Γ
psimplify1 (Not False)   = True
psimplify1 (Not True)    = False
psimplify1 (Not (Not x)) = x
psimplify1 (And False y) = False
psimplify1 (And True y)  = y
psimplify1 (And x False) = False
psimplify1 (And x True)  = x
psimplify1 (Or False y)  = y
psimplify1 (Or True y)   = True
psimplify1 (Or x False)  = x
psimplify1 (Or x True)   = True
psimplify1 (Imp False y) = True
psimplify1 (Imp True y)  = y
psimplify1 (Imp x False) = Not x
psimplify1 (Imp x True)  = True
psimplify1 (Iff False y) = Not y
psimplify1 (Iff True y)  = y
psimplify1 (Iff x False) = Not x
psimplify1 (Iff x True)  = x
psimplify1  f            = f

psimplify : Formulaᵢ Γ → Formulaᵢ Γ
psimplify (Not x)   = psimplify1 (Not (psimplify x))
psimplify (And x y) = psimplify1 (And (psimplify x) (psimplify y))
psimplify (Or x y)  = psimplify1 (Or (psimplify x) (psimplify y))
psimplify (Imp x y) = psimplify1 (Imp (psimplify x) (psimplify y))
psimplify (Iff x y) = psimplify1 (Iff (psimplify x) (psimplify y))
psimplify  f        = f

{-
_ : Imp (Not (Atom "x")) (Not (Atom "y")) ∈ (psimplify <$> parseForm "(true => (x <=> false)) => ~(y \\/ false /\\ z)")
_ = hereₘ refl

_ : True ∈ (psimplify <$> parseForm "((x => y) => true) \\/ ~false")
_ = hereₘ refl
-}

-- NNF
-- TODO use ELits

data NNF (Γ : LFSet A) : 𝒰 where
  LitF   : Lit Γ → NNF Γ
  TrueF  : NNF Γ
  FalseF : NNF Γ
  AndF   : NNF Γ → NNF Γ → NNF Γ
  OrF    : NNF Γ → NNF Γ → NNF Γ

nnf→form : {Γ : LFSet A} → NNF Γ → Formulaᵢ Γ
nnf→form (LitF l)   = lit→form l
nnf→form  TrueF     = True
nnf→form  FalseF    = False
nnf→form (AndF x y) = And (nnf→form x) (nnf→form y)
nnf→form (OrF x y)  = Or (nnf→form x) (nnf→form y)

mutual
  nnf : Formulaᵢ Γ → NNF Γ
  nnf  False    = FalseF
  nnf  True     = TrueF
  nnf (Atom a)  = LitF (Pos a)
  nnf (Not x)   = nnfNot x
  nnf (And x y) = AndF (nnf x) (nnf y)
  nnf (Or x y)  = OrF (nnf x) (nnf y)
  nnf (Imp x y) = OrF (nnfNot x) (nnf y)
  nnf (Iff x y) = OrF (AndF (nnf x) (nnf y)) (AndF (nnfNot x) (nnfNot y))

  nnfNot : Formulaᵢ Γ → NNF Γ
  nnfNot  False    = TrueF
  nnfNot  True     = FalseF
  nnfNot (Atom a)  = LitF (Neg a)
  nnfNot (Not x)   = nnf x
  nnfNot (And x y) = OrF (nnfNot x) (nnfNot y)
  nnfNot (Or x y)  = AndF (nnfNot x) (nnfNot y)
  nnfNot (Imp x y) = AndF (nnf x) (nnfNot y)
  nnfNot (Iff x y) = OrF (AndF (nnf x) (nnfNot y)) (AndF (nnfNot x) (nnf y))

nnf0 : Formulaᵢ Γ → NNF Γ
nnf0 = nnf ∘ psimplify

{-
fm : Maybe Form
fm = parseForm "(p <=> q) <=> ~(r => s)"

fm′ : Maybe Form
fm′ = (nnf→form ∘ nnf0) <$> fm

_ : "(p ∧ q ∨ ¬p ∧ ¬q) ∧ r ∧ ¬s ∨ (p ∧ ¬q ∨ ¬p ∧ q) ∧ (¬r ∨ s)" ∈ (prettyF <$> fm′)
_ = hereₘ refl

_ : true ∈ map² (λ a b → tautology (Iff a b)) fm fm′
_ = hereₘ refl
-}

-- NENF
-- TODO use ELits

data NENF (Γ : LFSet A) : 𝒰 where
  LitEF   : Lit Γ → NENF Γ
  TrueEF  : NENF Γ
  FalseEF : NENF Γ
  AndEF   : NENF Γ → NENF Γ → NENF Γ
  OrEF    : NENF Γ → NENF Γ → NENF Γ
  IffEF   : NENF Γ → NENF Γ → NENF Γ

wk-nenf : {Γ Δ : LFSet A}
        → Γ ⊆ Δ → NENF Γ → NENF Δ
wk-nenf s (LitEF l)   = LitEF (wk-lit s l)
wk-nenf s  TrueEF     = TrueEF
wk-nenf s  FalseEF    = FalseEF
wk-nenf s (AndEF x y) = AndEF (wk-nenf s x) (wk-nenf s y)
wk-nenf s (OrEF x y)  = OrEF (wk-nenf s x) (wk-nenf s y)
wk-nenf s (IffEF x y) = IffEF (wk-nenf s x) (wk-nenf s y)

nenf→formᵢ : NENF Γ  → Formulaᵢ Γ
nenf→formᵢ (LitEF l)   = lit→form l
nenf→formᵢ  TrueEF     = True
nenf→formᵢ  FalseEF    = False
nenf→formᵢ (AndEF x y) = And (nenf→formᵢ x) (nenf→formᵢ y)
nenf→formᵢ (OrEF x y)  = Or (nenf→formᵢ x) (nenf→formᵢ y)
nenf→formᵢ (IffEF x y) = Iff (nenf→formᵢ x) (nenf→formᵢ y)

wk-nenf-form : {Γ Δ : LFSet A} {s : Γ ⊆ Δ}
             → (f : NENF Γ)
             → nenf→formᵢ (wk-nenf s f) ＝ wk s (nenf→formᵢ f)
wk-nenf-form {s} (LitEF l) = wk-lit-form l
wk-nenf-form {s} TrueEF = refl
wk-nenf-form {s} FalseEF = refl
wk-nenf-form {s} (AndEF x y) =
  ap² {C = λ _ _ → Formulaᵢ _}
    And (wk-nenf-form x) (wk-nenf-form y)
wk-nenf-form {s} (OrEF x y) =
  ap² {C = λ _ _ → Formulaᵢ _}
    Or (wk-nenf-form x) (wk-nenf-form y)
wk-nenf-form {s} (IffEF x y) =
  ap² {C = λ _ _ → Formulaᵢ _}
    Iff (wk-nenf-form x) (wk-nenf-form y)

height-nenf : NENF Γ → ℕ
height-nenf = height ∘ nenf→formᵢ

height-nenf-wk : {Γ Δ : LFSet A} {s : Γ ⊆ Δ}
               → (f : NENF Γ)
               → height-nenf (wk-nenf s f) ＝ height-nenf f
height-nenf-wk {s} f =
 ap height (wk-nenf-form f) ∙ height-wk (nenf→formᵢ f)

mutual
  nenf : Formulaᵢ Γ → NENF Γ
  nenf  False    = FalseEF
  nenf  True     = TrueEF
  nenf (Atom a)  = LitEF (Pos a)
  nenf (Not x)   = nenfNot x
  nenf (And x y) = AndEF (nenf x) (nenf y)
  nenf (Or x y)  = OrEF (nenf x) (nenf y)
  nenf (Imp x y) = OrEF (nenfNot x) (nenf y)
  nenf (Iff x y) = IffEF (nenf x) (nenf y)

  nenfNot : Formulaᵢ Γ → NENF Γ
  nenfNot  False    = TrueEF
  nenfNot  True     = FalseEF
  nenfNot (Atom a)  = LitEF (Neg a)
  nenfNot (Not x)   = nenf x
  nenfNot (And x y) = OrEF (nenfNot x) (nenfNot y)
  nenfNot (Or x y)  = AndEF (nenfNot x) (nenfNot y)
  nenfNot (Imp x y) = AndEF (nenf x) (nenfNot y)
  nenfNot (Iff x y) = IffEF (nenf x) (nenfNot y)

nenf0 : Formulaᵢ Γ → NENF Γ
nenf0 = nenf ∘ psimplify

{-
_ : true ∈ (tautology <$> parseForm "(p => p') /\\ (q => q') => (p /\\ q => p' /\\ q')")
_ = hereₘ refl

_ : true ∈ (tautology <$> parseForm "(p => p') /\\ (q => q') => (p \\/ q => p' \\/ q')")
_ = hereₘ refl
-}

-- TODO (anti)monotonicity

-- DNF
-- satisfiability checking for a formula in DNF is easy

list-conj : List (Formulaᵢ Γ) → Formulaᵢ Γ
list-conj = Maybe.rec True (foldr₁ And) ∘ List⁺.from-list

list-conjΣ : List (Σ[ Γ ꞉ Ctx ] (Formulaᵢ Γ)) → Σ[ Γ ꞉ Ctx ] (Formulaᵢ Γ)
list-conjΣ =
    Maybe.rec ([] , True)
              (foldr₁ (λ where (Γ , f) (Δ , g) →
                                 (Γ ∪∷ Δ) , And (wk  ⊆-∪∷-l           f)
                                                (wk (⊆-∪∷-r {s₁ = Γ}) g)))
  ∘ List⁺.from-list

list-disj : List (Formulaᵢ Γ) → Formulaᵢ Γ
list-disj = Maybe.rec False (foldr₁ Or) ∘ List⁺.from-list

list-disjΣ : List (Σ[ Γ ꞉ Ctx ] (Formulaᵢ Γ)) → Σ[ Γ ꞉ Ctx ] (Formulaᵢ Γ)
list-disjΣ =
    Maybe.rec ([] , False)
              (foldr₁ (λ where (Γ , f) (Δ , g) →
                                 (Γ ∪∷ Δ) , Or (wk  ⊆-∪∷-l           f)
                                               (wk (⊆-∪∷-r {s₁ = Γ}) g)))
  ∘ List⁺.from-list

mklits : {Γ : LFSet A}
       → List (Formulaᵢ Γ) → Val Γ → Formulaᵢ Γ
mklits pvs v = list-conj $ map (λ p → if eval p v then p else Not p) pvs
  --   map (λ p → if eval p v then p else Not p) pvs

all-sat-vals : ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
             → (Val Γ → Bool)
             → Val Γ → List A → List (Val Γ)
all-sat-vals s v  []      = if s v then v ∷ [] else []
all-sat-vals s v (p ∷ ps) =
     all-sat-vals s (modify p false v) ps
  ++ all-sat-vals s (modify p true v) ps

dnf-naive : {Γ : LFSet A}
          → ⦃ d : is-discrete A ⦄
          → Formulaᵢ Γ → Formulaᵢ Γ
dnf-naive f =
  let ps = varsᵢ f
      sv = all-sat-vals (eval f) (λ _ → false) ps
    in
  list-disj $
  map (mklits (List.map-with-∈ ps (λ a a∈ →
   let a∈' = varsᵢ-⊆ {f = f}
               (map-⊆ unvar (ope→subset (nub-ope {cmp = _=?_})) a∈)
             in
   Atom (av a a∈')))) sv

{-
fm1 : String
fm1 = "(p \\/ q /\\ r) /\\ (~p \\/ ~r)"

fmP : Maybe Form
fmP = parseForm fm1
-}

{-
_ : "(p ∨ q ∧ r) ∧ (¬p ∨ ¬r)" ∈ (prettyF <$> fmP)
_ = hereₘ refl

_ : "¬p ∧ q ∧ r ∨ p ∧ ¬q ∧ ¬r ∨ p ∧ q ∧ ¬r" ∈ (prettyF ∘ dnf-naive <$> fmP)
_ = hereₘ refl
-}

distribAnd : Formulaᵢ Γ → Formulaᵢ Γ → Formulaᵢ Γ
distribAnd (Or p q)  r       = Or (distribAnd p r) (distribAnd q r)
distribAnd  p       (Or q r) = Or (distribAnd p q) (distribAnd p r)
distribAnd  p        q       = And p q

rawdnf : Formulaᵢ Γ → Formulaᵢ Γ
rawdnf (And x y) = distribAnd (rawdnf x) (rawdnf y)
rawdnf (Or x y)  = Or (rawdnf x) (rawdnf y)
rawdnf  f        = f

{-
_ : "(p ∧ ¬p ∨ p ∧ ¬r) ∨ (q ∧ r) ∧ ¬p ∨ (q ∧ r) ∧ ¬r" ∈ (prettyF ∘ rawdnf <$> fmP)
_ = hereₘ refl
-}

-- TODO use LFSet

Conjunct : LFSet A → 𝒰
Conjunct Γ = List (Lit Γ)

DNF : LFSet A → 𝒰
DNF Γ = List (Conjunct Γ)

dnf→form : DNF Γ → Formulaᵢ Γ
dnf→form = list-disj ∘ map (list-conj ∘ map lit→form)

distrib : {Γ : LFSet A}
        → ⦃ d : is-discrete A ⦄
        → DNF Γ → DNF Γ → DNF Γ
distrib s1 s2 = nub _=?_ $ map² union s1 s2 -- TODO better names / API

purednf : {Γ : LFSet A}
        → ⦃ d : is-discrete A ⦄
        → NNF Γ → DNF Γ
purednf (LitF l)   = (l ∷ []) ∷ []
purednf  TrueF     = [] ∷ []
purednf  FalseF    = []
purednf (AndF x y) = distrib (purednf x) (purednf y)
purednf (OrF x y)  = union (purednf x) (purednf y)

{-
_ : (  (Pos "p" ∷ Neg "p" ∷ [])
     ∷ (Pos "p" ∷ Neg "r" ∷ [])
     ∷ (Pos "q" ∷ Pos "r" ∷ Neg "p" ∷ [])
     ∷ (Pos "q" ∷ Pos "r" ∷ Neg "r" ∷ [])
     ∷ []) ∈ (purednf ∘ nnf <$> fmP)
_ = hereₘ refl

_ : (  (Pos "p" ∷ Neg "r" ∷ [])
     ∷ (Pos "q" ∷ Pos "r" ∷ Neg "p" ∷ [])
     ∷ []) ∈ (filter (not ∘ trivial?) ∘ purednf ∘ nnf <$> fmP)
_ = hereₘ refl
-}

simpdnf : {Γ : LFSet A}
        → ⦃ d : is-discrete A ⦄
        → Formulaᵢ Γ → DNF Γ
simpdnf f =
  let djs = filter nontrivial? $ purednf $ nnf f in
  filter (λ c → not (any (λ c′ → psubset? c′ c) djs)) djs

dnf : {Γ : LFSet A}
    → ⦃ d : is-discrete A ⦄
    → Formulaᵢ Γ → Formulaᵢ Γ
dnf = dnf→form ∘ simpdnf

{-
fmpD : Maybe Form
fmpD = dnf <$> fmP
-}
{-
_ : "p ∧ ¬r ∨ q ∧ r ∧ ¬p" ∈ (prettyF <$> fmpD)
_ = hereₘ refl

_ : true ∈ (map² (λ x y → tautology $ Iff x y) fmP fmpD)
_ = hereₘ refl
-}

-- CNF
-- tautology checking for a formula in CNF is easy

Clause : LFSet A → 𝒰
Clause Γ = List (Lit Γ)

opaque
  unfolding mapₛ
  avoid-var-clause : ⦃ d : is-discrete A ⦄
                     {v : A}
                   → (c : Clause Γ)
                   → v ∉ mapₛ unlit (LFSet.from-list c)
                   → Clause (rem v Γ)
  avoid-var-clause []      v∉ = []
  avoid-var-clause (l ∷ c) v∉ =
      avoid-lit-var l (fst $ ∉ₛ-uncons v∉)
    ∷ avoid-var-clause c (snd $ ∉ₛ-uncons v∉)

  avoid-ctx-clause : ⦃ d : is-discrete A ⦄
                   → (f : Clause Γ)
                   → {Δ : LFSet A}
                   → mapₛ unlit (LFSet.from-list f) ∥ₛ Δ
                   → Clause (minus Γ Δ)
  avoid-ctx-clause []      d = []
  avoid-ctx-clause (l ∷ f) d =
      avoid-lit-ctx l (fst $ ∥ₛ-∷-l← d)
    ∷ avoid-ctx-clause f (snd $ ∥ₛ-∷-l← d)

CNF : LFSet A → 𝒰
CNF Γ = List (Clause Γ)

cnf→form : CNF Γ → Formulaᵢ Γ
cnf→form = list-conj ∘ map (list-disj ∘ map lit→form)

purecnf : {Γ : LFSet A}
        → ⦃ d : is-discrete A ⦄
        → Formulaᵢ Γ → CNF Γ
purecnf = image (image negate) ∘ purednf ∘ nnfNot

simpcnf : {Γ : LFSet A}
        → ⦃ d : is-discrete A ⦄
        → Formulaᵢ Γ → CNF Γ
simpcnf f =
  let cjs = filter nontrivial? $ purecnf f in
  filter (λ c → not (any (λ c′ → psubset? c′ c) cjs)) cjs

cnf : {Γ : LFSet A}
    → ⦃ d : is-discrete A ⦄
    → Formulaᵢ Γ → Formulaᵢ Γ
cnf = cnf→form ∘ simpcnf

{-
fmpC : Maybe Form
fmpC = cnf <$> fmP
-}
{-
_ : "(p ∨ q) ∧ (p ∨ r) ∧ (¬p ∨ ¬r)" ∈ (prettyF <$> fmpC)
_ = hereₘ refl

_ : true ∈ (map² (λ x y → tautology $ Iff x y) fmP fmpC)
_ = hereₘ refl
-}

-- main : Main
-- main = run $ do put-str-ln $ Maybe.rec "" truth-table fmP

