module ch2.Stalmarck where

open import Foundations.Prelude
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

Eqv : 𝒰 → 𝒰
Eqv A = ELit A × ELit A

instance
  Show-eqv : ⦃ s : Show A ⦄ → Show (Eqv A)
  Show-eqv = default-show λ where
                              (p , q) → show p ++ₛ "<=>" ++ₛ show q

EClass : 𝒰 → 𝒰
EClass A = Partition (ELit A)

-- triplets

data Duplet (A : 𝒰) : 𝒰 where
  duand : ELit A → ELit A → Duplet A
  duor  : ELit A → ELit A → Duplet A
  -- we never get this
--  duimp : ELit A → ELit A → Duplet A
  duiff : ELit A → ELit A → Duplet A

is-duand : Duplet A → Type
is-duand (duand _ _) = ⊤
is-duand  _         = ⊥

is-duor : Duplet A → Type
is-duor (duor _ _) = ⊤
is-duor  _        = ⊥

duand≠duor : {p q r s : ELit A} → duand p q ≠ duor r s
duand≠duor e = subst is-duand e tt

duand≠duiff : {p q r s : ELit A} → duand p q ≠ duiff r s
duand≠duiff e = subst is-duand e tt

duor≠duiff : {p q r s : ELit A} → duor p q ≠ duiff r s
duor≠duiff e = subst is-duor e tt

unduplet : Duplet A → ELit A × ELit A
unduplet (duand p q) = p , q
unduplet (duor  p q) = p , q
unduplet (duiff p q) = p , q

Duplet-= : (A → A → Bool)
         → Duplet A → Duplet A → Bool
Duplet-= e (duand p1 q1) (duand p2 q2) = elit-= e p1 p2 and elit-= e q1 q2
Duplet-= e (duor  p1 q1) (duor  p2 q2) = elit-= e p1 p2 and elit-= e q1 q2
Duplet-= e (duiff p1 q1) (duiff p2 q2) = elit-= e p1 p2 and elit-= e q1 q2
Duplet-= e _              _              = false

Reflects-duplet : {e : A → A → Bool}
                → ⦃ r : ∀ {x y} → Reflects (x ＝ y) (e x y) ⦄
                → ∀ {d1 d2} → Reflects (d1 ＝ d2) (Duplet-= e d1 d2)
Reflects-duplet {e} ⦃ r ⦄ {d1 = duand p1 q1} {d2 = duand p2 q2} =
  Reflects.dmap ((λ e → ap² duand e) $²_) (contra (×-path-inv ∘ ap unduplet))
    (Reflects-× ⦃ rp = Reflects-elit r ⦄ ⦃ rq = Reflects-elit r ⦄)
Reflects-duplet {e} ⦃ r ⦄ {d1 = duand p1 q1} {d2 = duor p2 q2} =
  ofⁿ duand≠duor
Reflects-duplet {e} ⦃ r ⦄ {d1 = duand p1 q1} {d2 = duiff p2 q2} =
  ofⁿ duand≠duiff
Reflects-duplet {e} ⦃ r ⦄ {d1 = duor p1 q1} {d2 = duand p2 q2} =
  ofⁿ (duand≠duor ∘ _⁻¹)
Reflects-duplet {e} ⦃ r ⦄ {d1 = duor p1 q1} {d2 = duor p2 q2} =
  Reflects.dmap ((λ e → ap² duor e) $²_) (contra (×-path-inv ∘ ap unduplet))
    (Reflects-× ⦃ rp = Reflects-elit r ⦄ ⦃ rq = Reflects-elit r ⦄)
Reflects-duplet {e} ⦃ r ⦄ {d1 = duor p1 q1} {d2 = duiff p2 q2} =
  ofⁿ duor≠duiff
Reflects-duplet {e} ⦃ r ⦄ {d1 = duiff p1 q1} {d2 = duand p2 q2} =
  ofⁿ (duand≠duiff ∘ _⁻¹)
Reflects-duplet {e} ⦃ r ⦄ {d1 = duiff p1 q1} {d2 = duor p2 q2} =
  ofⁿ (duor≠duiff ∘ _⁻¹)
Reflects-duplet {e} ⦃ r ⦄ {d1 = duiff p1 q1} {d2 = duiff p2 q2} =
  Reflects.dmap ((λ e → ap² duiff e) $²_) (contra (×-path-inv ∘ ap unduplet))
    (Reflects-× ⦃ rp = Reflects-elit r ⦄ ⦃ rq = Reflects-elit r ⦄)

instance
  Duplet-discrete : ⦃ d : is-discrete A ⦄
                  → is-discrete (Duplet A)
  Duplet-discrete ⦃ d ⦄ {x} {y} .does  = Duplet-= (λ x y → d .does) x y
  Duplet-discrete ⦃ d ⦄ {x} {y} .proof = Reflects-duplet

Triplet : 𝒰 → 𝒰
Triplet A = A × Duplet A

tripatoms : Triplet A → List A
tripatoms (v , d) =
  let (l , r) = unduplet d in
  v ∷ Maybe.rec [] ((_∷ []) ∘ unlit) (unelit l) ++ Maybe.rec [] ((_∷ []) ∘ unlit) (unelit r)

-- TODO backport to def CNF?

TFM : 𝒰
TFM = FMap (Duplet Var) (Triplet Var)

Trp : 𝒰
Trp = ELit Var × TFM × ℕ

mk-prp : State ℕ Var
mk-prp .run-stateT n = suc n , "p_" ++ₛ show-ℕ n

mutual
  maintrip : NENF Var → TFM → ℕ
           → Trp
  maintrip (AndEF p q) defs n = defstp duand p q defs n
  maintrip (OrEF p q)  defs n = defstp duor p q defs n
  maintrip (IffEF p q) defs n = defstp duiff p q defs n
  maintrip (LitEF l)   defs n = elit l , defs , n
  maintrip  TrueEF     defs n = etrue , defs , n
  maintrip  FalseEF    defs n = efalse , defs , n

  defstp : (ELit Var → ELit Var → Duplet Var)
          → NENF Var → NENF Var → TFM → ℕ
          → Trp
  defstp op p q defs n =
    let (l1 , defs1 , n1) = maintrip p defs n
        (l2 , defs2 , n2) = maintrip q defs1 n1
        d' = op l1 l2
      in
    Maybe.rec
       (let (n3 , v) = mk-prp .run-stateT n2 in
          elit (Pos v)
        , upd d' (v , d') defs2
        , n3)
       (λ (v , _) → elit (Pos v) , defs2 , n2)
       (lup defs2 d')

triplicate : Form → ELit Var × List (Triplet Var)
triplicate fm =
  let fm' = nenf0 fm
      n = suc (over-atoms (max-var-ix "p_") (nenf→form fm') 0)
      (l , defs , _) = maintrip fm' emp n
    in
  l , codom defs

-- simple rules

align-pol : Eqv A → Eqv A
align-pol (p , q) =
  if enegative p
    then enegate p , enegate q
    else p , q

align : Eqv Var → Eqv Var
align (p , q) =
  if elit-< _<str?_ (eabs p) (eabs q)
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
      npairs = filter (λ (p , q) → not (eabs p =? eabs q)) pairs
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

inst-trigger : Var × ELit Var × ELit Var → List Trigger → List Trigger
inst-trigger = map ∘ instnfn
  where
  instfn : Var × ELit Var × ELit Var → ELit Var → ELit Var
  instfn (x , y , z) e =
    let sub : KVMap (ELit Var) (ELit Var)
        sub = insertm (elit $ Pos "p") (elit $ Pos x) $
              insertm (elit $ Pos "q") y $
              insertm (elit $ Pos "r") z $
              emptym
      in
    Maybe.rec e id (lookupm sub e)
  inst2fn : Var × ELit Var × ELit Var → Eqv Var → Eqv Var
  inst2fn i (p , q) = align (instfn i p , instfn i q)
  instnfn : Var × ELit Var × ELit Var → Trigger → Trigger
  instnfn i (a , c) = inst2fn i a , map (inst2fn i) c

trigger' : (Form → Form → Form) → List Trigger
trigger' op = triggers $ Iff (Atom "p") (op (Atom "q") (Atom "r"))

trigger : Triplet Var → List Trigger
trigger (x , duand y z) = inst-trigger (x , y , z) $ trigger' And
trigger (x , duor  y z) = inst-trigger (x , y , z) $ trigger' Or
trigger (x , duiff y z) = inst-trigger (x , y , z) $ trigger' Iff

-- 0-saturation

ListMap : 𝒰 → 𝒰 → 𝒰
ListMap K V = KVMap K (List V)

look : {K V : 𝒰} ⦃ d : is-discrete K ⦄ → ListMap K V → K → List V
look m l = Maybe.rec [] id (lookupm m l)

TrigMap : 𝒰
TrigMap = ListMap (ELit Var) Trigger

relevance : List Trigger → TrigMap
relevance trigs =
  List.rec (the TrigMap emptym) insert-relevant2 trigs
  where
  insert-relevant : ELit Var → Trigger → TrigMap → TrigMap
  insert-relevant p trg f =
    insertm p (insert-s trg (look f p)) f
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
          sp-pos = look rfn p
          sp-neg = look rfn p'
          sq-pos = look rfn q
          sq-neg = look rfn q'
          rfn' = insertm (canonize eqv' p)  (union sp-pos sq-pos) $
                 insertm (canonize eqv' p') (union sp-neg sq-neg) rfn
          nw = union (intersect sp-pos sq-pos) (intersect sp-neg sq-neg)
        in
      (List.rec [] (union ∘ snd) nw) , (eqv' , rfn')

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

RevMap : 𝒰
RevMap = ListMap (ELit Var) (ELit Var)

{-# TERMINATING #-}
inter : List (ELit Var)
      → Erf → Erf
      → RevMap → RevMap
      → Erf → Erf
inter []       _              _              _    _    erf = erf
inter (x ∷ xs) erf1@(eq1 , _) erf2@(eq2 , _) rev1 rev2 erf =
  let b1 = canonize eq1 x
      b2 = canonize eq2 x
      s1 = look rev1 b1
      s2 = look rev2 b2
      s = intersect s1 s2
    in
  inter (diff xs s) erf1 erf2 rev1 rev2 (equateset s erf)

reverseq : List (ELit Var) → EClass Var → RevMap
reverseq domain eqv =
  let a1 = map (λ x → x , canonize eqv x) domain in
  fold-r (λ (y , x) f → insertm x (insert-s y (look f x)) f) emptym a1

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

EqvMap : 𝒰
EqvMap = ListMap (Eqv Var) (Eqv Var)

stalmarck : Form → Maybe Bool
stalmarck fm =
  let fm' = psimplify (Not fm) in
  if fm' =? False
    then just true
    else
      if fm' =? True
        then just false
        else
          let pt = triplicate fm'
              p = pt .fst
              trips = pt .snd
              trigfn = List.rec emptym (λ f m → List.rec m include-trig (trigger f)) trips
              vars = map (elit ∘ Pos) (unions $ map tripatoms trips)
            in
          saturate-upto vars 0 2 (trigfn .kv) ((p , etrue) ∷ [])
  where
  include-trig : Trigger → EqvMap → EqvMap
  include-trig (e , cqs) f = insertm e (union cqs (look f e)) f

main : Main
main = run $ do put-str-ln $ show $ stalmarck $ mk-adder-test 1 1
                put-str-ln $ show $ stalmarck $ mk-adder-test 1 2
                put-str-ln $ show $ stalmarck $ mk-adder-test 2 1
                put-str-ln $ show $ stalmarck $ mk-adder-test 2 2
