{-# OPTIONS --no-exact-split #-}
module ch2.CNF where

open import Foundations.Prelude
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
open decminmax ℕ-dec-total

open import FMap
open import ListSet
open import ch2.Formula
open import ch2.Sem
open import ch2.NF

private variable
  A : 𝒰

{-
_ : "(¬p ∨ ¬q ∨ r) ∧ (¬p ∨ q ∨ ¬r) ∧ (p ∨ ¬q ∨ ¬r) ∧ (p ∨ q ∨ r)"
      ∈ (prettyF ∘ cnf <$> parseForm "p <=> (q <=> r)")
_ = hereₘ refl
-}

-- TODO psubst theorem

mk-prop : State ℕ Form
mk-prop .run-stateT n = suc n , Atom ("p_" ++ₛ show-ℕ n)

-- definitional CNF

FM : 𝒰
FM = FMap Form (Form × Form)

Trip : 𝒰
Trip = Form × FM × ℕ

mutual
  maincnf : Form → FM → ℕ
          → Trip
  maincnf (And p q) defs n = defstep And p q defs n
  maincnf (Or p q)  defs n = defstep Or p q defs n
  maincnf (Iff p q) defs n = defstep Iff p q defs n
  maincnf  f        defs n = (f , defs , n)

  defstep : (Form → Form → Form)
          → Form → Form → FM → ℕ
          → Trip
  defstep op p q defs n =
    let (fm1 , defs1 , n1) = maincnf p defs n
        (fm2 , defs2 , n2) = maincnf q defs1 n1
        fm' = op fm1 fm2
      in
    Maybe.rec (let (n3 , v) = mk-prop .run-stateT n2 in
                 v
               , upd fm' (v , Iff v fm') defs2
               , n3)
              (λ (v , _) → v , defs2 , n2)
              (lup defs2 fm')

max-var-ix : String → String → ℕ → ℕ
max-var-ix pfx s n =
  let m = lengthₛ pfx
      l = lengthₛ s
    in
  if (l ≤? m) or not (substring 0 m s =ₛ pfx)
    then n
    else (Maybe.rec n (max n) $
          parseℕ $ substring m (l ∸ m) s)

mk-defcnf : (Form → FM → ℕ → Trip) → Form → CNF Var
mk-defcnf fn fm =
  let fm' = nenf→form $ nenf0 fm
      n = suc (over-atoms (max-var-ix "p_") fm' 0)
      (fm'' , defs , _) = fn fm' emp n
      deflist = map snd (codom defs)
    in
  unions (simpcnf fm'' ∷ map simpcnf deflist)

defcnf : Form → Form
defcnf = cnf→form ∘ mk-defcnf maincnf

-- optimizations

-- had to inline

mutual
  sub-or-cnf : Form → Form → FM → ℕ
             → Trip
  sub-or-cnf p q defs n =
    let (fm1 , defs1 , n1) = or-cnf p defs n
        (fm2 , defs2 , n2) = or-cnf q defs1 n1
      in
    (Or fm1 fm2 , defs2 , n2)

  or-cnf : Form → FM → ℕ → Trip
  or-cnf (Or p q) = sub-or-cnf p q
  or-cnf  f       = maincnf f

mutual
  sub-and-cnf : Form → Form → FM → ℕ
              → Trip
  sub-and-cnf p q defs n =
    let (fm1 , defs1 , n1) = and-cnf p defs n
        (fm2 , defs2 , n2) = and-cnf q defs1 n1
      in
    (And fm1 fm2 , defs2 , n2)

  and-cnf : Form → FM → ℕ → Trip
  and-cnf (And p q) = sub-and-cnf p q
  and-cnf  f        = or-cnf f

defcnfs : Form → CNF Var
defcnfs = mk-defcnf and-cnf

defcnf' : Form → Form
defcnf' = cnf→form ∘ defcnfs

-- 3-CNF

mutual
  sub-and-cnf3 : Form → Form → FM → ℕ
               → Trip
  sub-and-cnf3 p q defs n =
    let (fm1 , defs1 , n1) = and-cnf3 p defs n
        (fm2 , defs2 , n2) = and-cnf3 q defs1 n1
      in
    (And fm1 fm2 , defs2 , n2)

  and-cnf3 : Form → FM → ℕ → Trip
  and-cnf3 (And p q) = sub-and-cnf3 p q
  and-cnf3  f        = maincnf f

defcnf3 : Form → Form
defcnf3 = cnf→form ∘ mk-defcnf and-cnf3

fm0 : String
fm0 = "p <=> (q <=> r)"

fm : String
fm = "(p \\/ (q /\\ ~r)) /\\ s"

{-
main : Main
main = run $ do put-str-ln $ ("naive cnf for " ++ₛ ppF id fm0)
                put-str-ln $ ppF cnf fm0
                let fms = ppF id fm
                put-str-ln $ ("def cnf for " ++ₛ fms)
                put-str-ln $ ppF defcnf fm
                put-str-ln $ ("optimized cnf for " ++ₛ fms)
                put-str-ln $ ppF defcnf' fm
                put-str-ln $ ("3-cnf for " ++ₛ fms)
                put-str-ln $ ppF defcnf3 fm
-}
