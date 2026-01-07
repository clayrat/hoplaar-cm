{-# OPTIONS --no-exact-split #-}
module ch2.Ix.CNF where

open import Foundations.Prelude
open Variadics _
open import Meta.Effect hiding (_>>_) renaming (_>>=_ to _>>=ᵐ_)
open import Meta.Effect.Bind.State
open import Logic.Discreteness
open import System.Everything hiding (_<$>_)

open import Data.Bool
open import Data.String
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Any renaming (here to hereₘ)
open import Data.List as List

open import Order.Diagram.Meet
open import Order.Constructions.Minmax
open import Order.Constructions.Nat
import Order.Diagram.Join.Reasoning as JR
open decminmax ℕ-dec-total
open JR ℕₚ max-joins

open import Induction.Nat.Strong as Box using (□_)

open import KVMapU

open import ListSet
open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Base 0ℓ

open import ch2.Formula
open import ch2.Ix.Formula
open import ch2.Ix.NF
open import ch2.Ix.Lit

private variable
--  A : 𝒰
  Γ Δ : LFSet String

{-
_ : "(¬p ∨ ¬q ∨ r) ∧ (¬p ∨ q ∨ ¬r) ∧ (p ∨ ¬q ∨ ¬r) ∧ (p ∨ q ∨ r)"
      ∈ (prettyF ∘ cnf <$> parseForm "p <=> (q <=> r)")
_ = hereₘ refl
-}

-- TODO psubst theorem

--mk-prop : State ℕ (Formulaᵢ ?)
--mk-prop .run-stateT n = suc n , Atom ("p_" ++ₛ show-ℕ n)

-- definitional CNF

open KVOps
open KVOps2

FM : Ctx → 𝒰
FM Γ = KVMap (Duplet Γ) (Triplet Γ)

wk-fm : Γ ⊆ Δ → FM Γ → FM Δ
wk-fm s =
  bimapm (wk-duplet s) wk-duplet-inj
    (λ where (v , d) → (wk-avar s v , wk-duplet s d))

Trip : Ctx → 𝒰
Trip Γ = ELit Γ × FM Γ × ℕ

-- induction on NENF height
NHI-ty : ℕ → 𝒰
NHI-ty x = {Θ : Ctx} → (f : NENF Θ) → x ＝ height-nenf f
                     → FM Θ → ℕ
                     → Σ[ Δ ꞉ Ctx ] (Trip (Δ ∪∷ Θ))

-- induction on a height of a product of NENFs
NHI×-ty : ℕ → 𝒰
NHI×-ty x = {Θ : Ctx} → (p : NENF Θ) → (q : NENF Θ) → x ＝ 1 + max (height-nenf p) (height-nenf q)
                      → FM Θ → ℕ
                      → Σ[ Δ ꞉ Ctx ] (Trip (Δ ∪∷ Θ))

-- TODO try defining Box for Formulas?
-- we only need WF here for a recursive call on `wk _ q`
defstep : ({Θ : Ctx} → ELit Θ → ELit Θ → Duplet Θ)
        → ∀[ □ NHI-ty ⇒ NHI×-ty ]
defstep op ih {Θ} p q e defs n =
  let (Δp , (el1 , defs1 , n1)) = Box.call ih (<-≤-trans (≤≃<suc $ l≤∪)
                                                         (=→≤ (e ⁻¹)))
                                              p refl defs n
      (Δq , (el2 , defs2 , n2)) = Box.call ih (<-≤-trans (≤-<-trans (=→≤ (height-nenf-wk q))
                                                                    (≤≃<suc $ r≤∪ {x = height-nenf p}))
                                                         (=→≤ (e ⁻¹)))
                                              (wk-nenf (⊆-∪∷-r {s₁ = Δp}) q) refl defs1 n1
      d' = op (wk-elit (⊆-∪∷-r {s₁ = Δq}) el1) el2
    in
  Maybe.rec
    -- add a new atom
    (let x = "p_" ++ₛ show-ℕ n2
         v = Pos (av x (⊆-∪∷-l {s₂ = Θ} (hereₛ {xs = Δq ∪∷ Δp} refl)))
         s : (Δq ∪∷ Δp ∪∷ Θ) ⊆ ((x ∷ Δq ∪∷ Δp) ∪∷ Θ)
         s = λ {x = z} → subst (z ∈_) (∪∷-assoc (x ∷ Δq)) ∘ thereₛ
       in
       x ∷ Δq ∪∷ Δp
     , elit v -- v
     , insertm (wk-duplet s d')
               (lit→atomvar v , wk-duplet s d')
               (wk-fm s defs2)
     , suc n2)
    (λ (v , _) →
         let s : (Δq ∪∷ Δp ∪∷ Θ) ⊆ ((Δq ∪∷ Δp) ∪∷ Θ)
             s = λ {x = z} → subst (z ∈_) (∪∷-assoc Δq)
           in
           (Δq ∪∷ Δp)
         , elit (Pos (wk-avar s v))
         , wk-fm s defs2
         , n2)
    (lookupm defs2 d')

maincnf-loop : ∀[ □ NHI-ty ⇒ NHI-ty ]
maincnf-loop ih (LitEF l)   eq defs n = [] , elit l , defs , n
maincnf-loop ih  TrueEF     eq defs n = [] , etrue , defs , n
maincnf-loop ih  FalseEF    eq defs n = [] , efalse , defs , n
maincnf-loop ih (AndEF p q) eq defs n = defstep duand ih p q eq defs n
maincnf-loop ih (OrEF p q)  eq defs n = defstep duor ih p q eq defs n
maincnf-loop ih (IffEF p q) eq defs n = defstep duiff ih p q eq defs n

maincnf : NENF Γ → FM Γ → ℕ
        → Σ[ Δ ꞉ Ctx ] (Trip (Δ ∪∷ Γ))
maincnf f defs n =
  Box.fix
    NHI-ty
    maincnf-loop
    f refl defs n

max-var-ix : String → String → ℕ → ℕ
max-var-ix pfx s n =
  let m = lengthₛ pfx
      l = lengthₛ s
    in
  if (l ≤? m) or not (substring 0 m s =ₛ pfx)
    then n
    else (Maybe.rec n (max n) $
          parseℕ $ substring m (l ∸ m) s)

TripF : Ctx → 𝒰
TripF Γ = Formulaᵢ Γ × FM Γ × ℕ

wk-exttrip : Σ[ Δ ꞉ Ctx ] (Trip (Δ ∪∷ Γ)) → Σ[ Δ ꞉ Ctx ] (TripF (Δ ∪∷ Γ))
wk-exttrip (Δ , (e , defs , n)) = Δ , (elit→form e , defs , n)

mk-defcnf : (NENF Γ → FM Γ → ℕ → Σ[ Δ ꞉ Ctx ] (TripF (Δ ∪∷ Γ)))
           → Formulaᵢ Γ        → Σ[ Δ ꞉ Ctx ] (CNF  (Δ ∪∷ Γ))
mk-defcnf fn fm =
  let fm' = nenf0 fm
      n = suc (over-varsᵢ (max-var-ix "p_") (nenf→formᵢ fm') 0)
      (Δ , e , defs , _) = fn fm' emptym n
      deflist = map snd (valsm defs)
    in
  Δ , unions (simpcnf (e) ∷ map (simpcnf ∘ duplet→form) deflist)

defcnf : Formulaᵢ Γ → Σ[ Δ ꞉ Ctx ] (Formulaᵢ (Δ ∪∷ Γ))
defcnf f =
  let Δc = mk-defcnf (λ ne f → wk-exttrip ∘ maincnf ne f) f in
  (Δc .fst , cnf→form (Δc . snd))

-- optimizations

-- WF again

-- induction on NENF height
NHIF-ty : ℕ → 𝒰
NHIF-ty x = {Θ : Ctx} → (f : NENF Θ) → x ＝ height-nenf f
                      → FM Θ → ℕ
                      → Σ[ Δ ꞉ Ctx ] (TripF (Δ ∪∷ Θ))

-- induction on a height of a product of NENFs
NHI×F-ty : ℕ → 𝒰
NHI×F-ty x = {Θ : Ctx} → (p : NENF Θ) → (q : NENF Θ) → x ＝ 1 + max (height-nenf p) (height-nenf q)
                       → FM Θ → ℕ
                       → Σ[ Δ ꞉ Ctx ] (TripF (Δ ∪∷ Θ))

subcnf : ({Θ : Ctx} → Formulaᵢ Θ → Formulaᵢ Θ → Formulaᵢ Θ)
       → ∀[ □ NHIF-ty ⇒ NHI×F-ty ]
subcnf op ih {Θ} p q e defs n =
  let (Δp , (f1 , defs1 , n1)) = Box.call ih (<-≤-trans (≤≃<suc $ l≤∪)
                                                         (=→≤ (e ⁻¹)))
                                              p refl defs n
      (Δq , (f2 , defs2 , n2)) = Box.call ih (<-≤-trans (≤-<-trans (=→≤ (height-nenf-wk q))
                                                                    (≤≃<suc $ r≤∪ {x = height-nenf p}))
                                                         (=→≤ (e ⁻¹)))
                                              (wk-nenf (⊆-∪∷-r {s₁ = Δp}) q) refl defs1 n1
      s : (Δq ∪∷ Δp ∪∷ Θ) ⊆ ((Δq ∪∷ Δp) ∪∷ Θ)
      s = λ {x = z} → subst (z ∈_) (∪∷-assoc Δq)
    in
    Δq ∪∷ Δp
  , op (wk (s ∘ ⊆-∪∷-r {s₁ = Δq}) f1)
       (wk  s                      f2)
  , wk-fm s defs2
  , n2

or-cnf-loop : ∀[ □ NHIF-ty ⇒ NHIF-ty ]
or-cnf-loop ih (OrEF p q) e defs n = subcnf Or ih p q e defs n
or-cnf-loop _   f         _ defs n = wk-exttrip $ maincnf f defs n

or-cnf : NENF Γ → FM Γ → ℕ → Σ[ Δ ꞉ Ctx ] (TripF (Δ ∪∷ Γ))
or-cnf f defs n =
  Box.fix
    NHIF-ty
    or-cnf-loop
    f refl defs n

and-cnf-loop : ∀[ □ NHIF-ty ⇒ NHIF-ty ]
and-cnf-loop ih (AndEF p q) e defs n = subcnf And ih p q e defs n
and-cnf-loop _   f          _ defs n = or-cnf f defs n

and-cnf : NENF Γ → FM Γ → ℕ → Σ[ Δ ꞉ Ctx ] (TripF (Δ ∪∷ Γ))
and-cnf f defs n =
  Box.fix
    NHIF-ty
    and-cnf-loop
    f refl defs n

defcnfs : Formulaᵢ Γ → Σ[ Δ ꞉ Ctx ] (CNF (Δ ∪∷ Γ))
defcnfs = mk-defcnf and-cnf

defcnf' : Formulaᵢ Γ → Σ[ Δ ꞉ Ctx ] (Formulaᵢ (Δ ∪∷ Γ))
defcnf' f =
  let Δc = defcnfs f in
  (Δc .fst , cnf→form (Δc . snd))

-- 3-CNF

and-cnf3-loop : ∀[ □ NHIF-ty ⇒ NHIF-ty ]
and-cnf3-loop ih (AndEF p q) e defs n = subcnf And ih p q e defs n
and-cnf3-loop _   f          _ defs n = wk-exttrip $ maincnf f defs n

and-cnf3 : NENF Γ → FM Γ → ℕ → Σ[ Δ ꞉ Ctx ] (TripF (Δ ∪∷ Γ))
and-cnf3 f defs n =
  Box.fix
    NHIF-ty
    and-cnf3-loop
    f refl defs n

defcnf3 : Formulaᵢ Γ → Σ[ Δ ꞉ Ctx ] (Formulaᵢ (Δ ∪∷ Γ))
defcnf3 f =
  let Δc = mk-defcnf and-cnf3 f in
  (Δc .fst , cnf→form (Δc . snd))

fm0 : String
fm0 = "p <=> (q <=> r)"

fm : String
fm = "(p \\/ (q /\\ ~r)) /\\ s"

{-
main : Main
main = run $ do put-str-ln $ ("naive cnf for " ++ₛ ppFᵢ id fm0)
                put-str-ln $ ppFᵢ cnf fm0
                let fms = ppFᵢ id fm
                put-str-ln $ ("def cnf for " ++ₛ fms)
                put-str-ln $ ppFΣᵢ defcnf fm
                put-str-ln $ ("optimized cnf for " ++ₛ fms)
                put-str-ln $ ppFΣᵢ defcnf' fm
                put-str-ln $ ("3-cnf for " ++ₛ fms)
                put-str-ln $ ppFΣᵢ defcnf3 fm
-}
