module ch2.Stalmarck where

open import Foundations.Prelude
open import Meta.Effect hiding (_>>_) renaming (_>>=_ to _>>=ᵐ_)
open import Meta.Show
open import Logic.Discreteness
open import System.Everything hiding (_<$>_)

open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec
open import Data.Nat
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.List.Operations.Discrete
open import Data.String

open import Order.Constructions.String

open import FMap
open import KVMapU
open import ListSet
open import UnionFind
open import ch2.Formula
open import ch2.Sem
open import ch2.NF
open import ch2.CNF
open import ch2.Appl

private variable
  A : 𝒰

open KVOps
open KVOps2
open KVProp

-- triplets

triplicate : Form → Form × List Form
triplicate fm =
  let fm' = nenf→form $ nenf0 fm
      n = suc (over-atoms (max-var-ix "p_") fm' 0)
      (fm'' , defs , _) = maincnf fm' emp n
    in
  fm'' , map snd (codom defs)

-- simple rules

lit-< : Lit Var → Lit Var → Bool
lit-< (Pos v1) (Pos v2) = v1 <str? v2
lit-< (Pos v1) (Neg v2) = true
lit-< (Neg v1) (Pos v2) = false
lit-< (Neg v1) (Neg v2) = v1 <str? v2

data ELit (A : 𝒰) : 𝒰 where
  elit : Lit A → ELit A
  etrue : ELit A
  efalse : ELit A

unelit : ELit A → Maybe (Lit A)
unelit (elit l) = just l
unelit _ = nothing

is-elit : ELit A → Type
is-elit (elit _) = ⊤
is-elit  _       = ⊥

is-etrue : ELit A → Type
is-etrue etrue = ⊤
is-etrue _     = ⊥

elit≠etrue : {l : Lit A} → elit l ≠ etrue
elit≠etrue p = subst is-elit p tt

elit≠efalse : {l : Lit A} → elit l ≠ efalse
elit≠efalse p = subst is-elit p tt

etrue≠efalse : etrue {A = A} ≠ efalse
etrue≠efalse p = subst is-etrue p tt

elit-= : (A → A → Bool)
       → ELit A → ELit A → Bool
elit-= e (elit l1) (elit l2) = Lit-= e l1 l2
elit-= e (elit _)  etrue     = false
elit-= e (elit _)  efalse    = false
elit-= e  etrue   (elit _)   = false
elit-= e  etrue    etrue     = true
elit-= e  etrue    efalse    = false
elit-= e  efalse  (elit _)   = false
elit-= e  efalse   etrue     = false
elit-= e  efalse   efalse    = true

Reflects-elit : {e : A → A → Bool}
              → (∀ {x y} → Reflects (x ＝ y) (e x y))
              → ∀ {lx ly} → Reflects (lx ＝ ly) (elit-= e lx ly)
Reflects-elit r {lx = elit l1} {ly = elit l2} =
  Reflects.dmap (ap elit) (contra (just-inj ∘ ap unelit))
    (Reflects-lit r {lx = l1} {ly = l2})
Reflects-elit r {lx = elit l1} {ly = etrue}   = ofⁿ elit≠etrue
Reflects-elit r {lx = elit l1} {ly = efalse}  = ofⁿ elit≠efalse
Reflects-elit r {lx = etrue}   {ly = elit l2} = ofⁿ (elit≠etrue ∘ _⁻¹)
Reflects-elit r {lx = etrue}   {ly = etrue}   = ofʸ refl
Reflects-elit r {lx = etrue}   {ly = efalse}  = ofⁿ etrue≠efalse
Reflects-elit r {lx = efalse}  {ly = elit l2} = ofⁿ (elit≠efalse ∘ _⁻¹)
Reflects-elit r {lx = efalse}  {ly = etrue}   = ofⁿ (etrue≠efalse ∘ _⁻¹)
Reflects-elit r {lx = efalse}  {ly = efalse}  = ofʸ refl

instance
  ELit-is-discrete : ⦃ d : is-discrete A ⦄ → is-discrete (ELit A)
  ELit-is-discrete ⦃ d ⦄ {x} {y} .does  = elit-= (λ x y → d {x = x} {y = y} .does) x y
  ELit-is-discrete ⦃ d ⦄         .proof = Reflects-elit (d .proof)

  Show-elit : ⦃ s : Show A ⦄ → Show (ELit A)
  Show-elit = default-show λ where
                              (elit l) → show l
                              etrue → "T"
                              efalse → "F"

elit-< : ELit Var → ELit Var → Bool
elit-< (elit l1) (elit l2) = lit-< l1 l2
elit-< (elit _)   etrue    = false
elit-< (elit _)   efalse   = false
elit-<  etrue    (elit _)  = true
elit-<  etrue     etrue    = false
elit-<  etrue     efalse   = true
elit-<  efalse   (elit _)  = true
elit-<  efalse    etrue    = false
elit-<  efalse    efalse   = false

elit→form : ELit A → Formula A
elit→form (elit l) = lit→form l
elit→form  etrue   = True
elit→form  efalse  = False

negelit : ELit A → ELit A
negelit (elit x) = elit (negate x)
negelit etrue = efalse
negelit efalse = etrue

form→elit : Formula A → Maybe (ELit A)
form→elit  False   = just efalse
form→elit  True    = just etrue
form→elit (Atom x) = just $ elit $ Pos x
form→elit (Not f)  = map negelit $ form→elit f
form→elit  _       = nothing

Eqv : 𝒰 → 𝒰
Eqv A = ELit A × ELit A

instance
  Show-eqv : ⦃ s : Show A ⦄ → Show (Eqv A)
  Show-eqv = default-show λ where
                              (p , q) → show p ++ₛ "<=>" ++ₛ show q

EClass : 𝒰 → 𝒰
EClass A = Partition (ELit A)

enegative : ELit A → Bool
enegative (elit (Neg _)) = true
enegative  efalse        = true
enegative  _             = false

epositive : ELit A → Bool
epositive = not ∘ enegative

enegate : ELit A → ELit A
enegate (elit l) = elit (negate l)
enegate  etrue   = efalse
enegate  efalse  = etrue

eatom : ELit A → ELit A
eatom lit = if enegative lit then enegate lit else lit

align-pol : Eqv A → Eqv A
align-pol (p , q) =
  if enegative p
    then enegate p , enegate q
    else p , q

align : Eqv Var → Eqv Var
align (p , q) =
  if elit-< (eatom p) (eatom q)
    then align-pol (q , p)
    else align-pol (p , q)

equate2 : ⦃ d : is-discrete A ⦄
        → Eqv A → EClass A → EClass A
equate2 (p , q) = equate (enegate p) (enegate q) ∘ equate p q

irredundant : ⦃ d : is-discrete A ⦄
            → EClass A → List (Eqv A) → List (Eqv A)
irredundant rel []              = []
irredundant rel ((p , q) ∷ eqs) =
  if canonize rel p =? canonize rel q
    then irredundant rel eqs
    else insert-s (p , q) (irredundant (equate2 (p , q) rel) eqs)

consequences : ⦃ d : is-discrete A ⦄
             → Eqv A → Formula A
             → List (Eqv A) → List (Eqv A)
consequences {A} (p , q) fm eqs =
  irredundant (equate2 (p , q) unequal) (filter follows eqs)
  where
  follows : ELit A × ELit A → Bool
  follows (r , s) =
    tautology $
    Imp (And (Iff (elit→form p) (elit→form q)) fm)
        (Iff (elit→form r) (elit→form s))

Trigger : 𝒰
Trigger = Eqv Var × List (Eqv Var)

instance
  Show-trigger : Show Trigger
  Show-trigger =
    default-show $
    λ where
        (pq , eqs) → "eqv: " ++ₛ show pq ++ₛ "\n" ++ₛ
                     "csq: " ++ₛ show eqs ++ₛ "\n"

alignedeqs : Form → List (Eqv Var)
alignedeqs fm =
  let poslits = insert-s etrue (map (elit ∘ Pos) (atoms fm))
      lits = union poslits (map enegate poslits)
      pairs = map² _,_ lits lits
      npairs = filter (λ (p , q) → not (eatom p =? eatom q)) pairs
   in
  setify (map align npairs)

triggers : Form → List Trigger
triggers fm =
  let eqs = alignedeqs fm
      raw = map (λ pq → pq , consequences pq fm eqs) eqs
    in
  filter (is-cons? ∘ snd) raw

{-
fms : String
fms = "p <=> (q /\\ r)"

mfs : Maybe Form
mfs = parseForm fms
-}

inst-trigger : Form × Form × Form → List Trigger → List Trigger
inst-trigger = map ∘ instnfn
  where
  ddnegate : Form → Form
  ddnegate (Not (Not f)) = f
  ddnegate  f            = f
  instfn : Form × Form × Form → ELit Var → ELit Var
  instfn (x , y , z) e =
    let sub : KVMap (ELit Var) Form
        sub = insertm (elit $ Pos "p") x $
              insertm (elit $ Pos "q") y $
              insertm (elit $ Pos "r") z $
              emptym
      in
    Maybe.rec
      e
      -- TODO triplicate should just produce ELits
      (Maybe.rec e id ∘ form→elit ∘ ddnegate)
      (lookupm sub e)
  inst2fn : Form × Form × Form → Eqv Var → Eqv Var
  inst2fn i (p , q) = align (instfn i p , instfn i q)
  instnfn : Form × Form × Form → Trigger → Trigger
  instnfn i (a , c) = inst2fn i a , map (inst2fn i) c

trigger' : (Form → Form → Form) → List Trigger
trigger' op = triggers $ Iff (Atom "p") (op (Atom "q") (Atom "r"))

trigger : Form → List Trigger
trigger (Iff x (And y z)) = inst-trigger (x , y , z) $ trigger' And
trigger (Iff x (Or y z))  = inst-trigger (x , y , z) $ trigger' Or
trigger (Iff x (Imp y z)) = inst-trigger (x , y , z) $ trigger' Imp
trigger (Iff x (Iff y z)) = inst-trigger (x , y , z) $ trigger' Iff
trigger _                 = []

-- 0-saturation

TrigMap : 𝒰
TrigMap = KVMap (ELit Var) (List Trigger)

relevance : List Trigger → TrigMap
relevance trigs =
  List.rec (the TrigMap emptym) insert-relevant2 trigs
  where
  insert-relevant : ELit Var → Trigger → TrigMap → TrigMap
  insert-relevant p trg f =
    insertm p (insert-s trg (Maybe.rec [] id (lookupm f p))) f
  insert-relevant2 : Trigger → TrigMap → TrigMap
  insert-relevant2 trg@((p , q) , _) =
    insert-relevant p trg ∘ insert-relevant q trg

Erf : 𝒰
Erf = EClass Var × TrigMap

equatecons : Eqv Var → Erf → List (Eqv Var) × Erf
equatecons (p0 , q0) erf@(eqv , rfn) =
  let p = canonize eqv p0
      q = canonize eqv q0
    in
  if p =? q
    then [] , erf
    else
      let p' = canonize eqv (negelit p0)
          q' = canonize eqv (negelit q0)
          eqv' = equate2 (p , q) eqv
          sp-pos = look p
          sp-neg = look p'
          sq-pos = look q
          sq-neg = look q'
          rfn' = insertm (canonize eqv' p)  (union sp-pos sq-pos) $
                 insertm (canonize eqv' p') (union sp-neg sq-neg) rfn
          nw = union (intersect sp-pos sq-pos) (intersect sp-neg sq-neg)
        in
      (List.rec [] (union ∘ snd) nw) , (eqv' , rfn')
  where
  look : ELit Var → List Trigger
  look f = Maybe.rec [] id (lookupm rfn f)

{-# TERMINATING #-}
zero-saturate : Erf → List (Eqv Var) → Erf
zero-saturate erf [] = erf
zero-saturate erf (pq ∷ a) =
  let ns , erf' = equatecons pq erf in
  zero-saturate erf' (union a ns)

zero-saturate-and-check : Erf → List (Eqv Var) → Erf
zero-saturate-and-check erf trigs =
  let erf' = zero-saturate erf trigs
      eqv' = erf' .fst
      vars = filter epositive (equated eqv')
    in
  if List.any (λ x → equivalent eqv' x (enegate x)) vars
    then snd (equatecons (etrue , efalse) erf')
    else erf'

truefalse : EClass Var → Bool
truefalse eqv = equivalent eqv efalse etrue

-- higher saturation

equateset : List (ELit Var) → Erf → Erf
equateset (a ∷ b ∷ ss) eqfn = equateset (b ∷ ss) (snd (equatecons (a , b) eqfn))
equateset _            eqfn = eqfn

{-# TERMINATING #-}
inter : List (ELit Var) → Erf → Erf
      → KVMap (ELit Var) (List (ELit Var))
      → KVMap (ELit Var) (List (ELit Var))
      → Erf → Erf
inter []       _              _              _    _    erf = erf
inter (x ∷ xs) erf1@(eq1 , _) erf2@(eq2 , _) rev1 rev2 erf =
  let b1 = canonize eq1 x
      b2 = canonize eq2 x
      s1 = Maybe.rec [] id (lookupm rev1 b1)
      s2 = Maybe.rec [] id (lookupm rev2 b2)
      s = intersect s1 s2
    in
  inter (diff xs s) erf1 erf2 rev1 rev2 (equateset s erf)

reverseq : List (ELit Var) → EClass Var → KVMap (ELit Var) (List (ELit Var))
reverseq domain eqv =
  let a1 = map (λ x → x , canonize eqv x) domain in
  fold-r (λ (y , x) f → insertm x (insert-s y (Maybe.rec [] id (lookupm f x))) f) emptym a1

stal-intersect : Erf → Erf → Erf → Erf
stal-intersect erf1@(eq1 , _) erf2@(eq2 , _) erf =
  if truefalse eq1 then erf2
    else if truefalse eq2 then erf1 else
      let dom1 = equated eq1
          dom2 = equated eq2
          comdom = intersect dom1 dom2
          rev1 = reverseq dom1 eq1
          rev2 = reverseq dom2 eq2
        in
      inter comdom erf1 erf2 rev1 rev2 erf

mutual
  {-# TERMINATING #-}
  saturate : ℕ → Erf → List (Eqv Var) → List (ELit Var) → Erf
  saturate n erf assigs allvars =
    let erf' = zero-saturate-and-check erf assigs
        eqv' = erf' .fst
      in
    if (n == 0) or truefalse eqv' then erf'
      else
        let erf'' = splits n erf' allvars allvars
            eqv'' = erf'' .fst
          in
         if eqv'' =? eqv' then erf''
           else saturate n erf'' [] allvars

  splits : ℕ → Erf → List (ELit Var) → List (ELit Var) → Erf
  splits _ erf           _       [] = erf
  splits n erf@(eqv , _) allvars (p ∷ vars) =
    if not (canonize eqv p =? p)
      then splits n erf allvars vars
      else let erf0 = saturate (pred n) erf ((p , efalse) ∷ []) allvars
               erf1 = saturate (pred n) erf ((p , etrue) ∷ []) allvars
               erf' = stal-intersect erf0 erf1 erf
               eqv' = erf' .fst
             in
            if truefalse eqv' then erf' else splits n erf' allvars vars

-- toplevel function

{-# TERMINATING #-}
saturate-upto : List (ELit Var) → ℕ → ℕ → List Trigger → List (Eqv Var) → Maybe Bool
saturate-upto vars n m trigs assigs =
  if m <? n then nothing
    else let eqv = saturate n (unequal , relevance trigs) assigs vars .fst in
         if truefalse eqv
           then just true
           else saturate-upto vars (suc n) m trigs assigs

stalmarck : Form → Maybe Bool
stalmarck fm =
  let fm' = psimplify (Not fm) in
  if fm' =? False
    then just true
    else if fm' =? True
           then just false
           else let pt = triplicate fm'
                    p = pt .fst
                    trips = pt .snd
                    trigfn = List.rec emptym (λ f m → List.rec m include-trig (trigger f)) trips
                    vars = map (elit ∘ Pos) (unions $ map atoms trips)
                  in
                -- TODO triplicate should just produce ELits
                Maybe.rec
                  nothing
                  (λ l → saturate-upto vars 0 2 (trigfn .kv) ((l , etrue) ∷ []))
                  (form→elit p)
  where
  include-trig : Trigger
               → KVMap (Eqv Var) (List (Eqv Var))
               → KVMap (Eqv Var) (List (Eqv Var))
  include-trig (e , cqs) f = insertm e (union cqs (Maybe.rec [] id (lookupm f e))) f

main : Main
main = run $ do put-str-ln $ show $ stalmarck $ mk-adder-test 1 1
                put-str-ln $ show $ stalmarck $ mk-adder-test 1 2
                put-str-ln $ show $ stalmarck $ mk-adder-test 2 1
                put-str-ln $ show $ stalmarck $ mk-adder-test 2 2

