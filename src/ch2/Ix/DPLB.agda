{-# OPTIONS --no-exact-split #-}
module ch2.Ix.DPLB where

open import Prelude
open import Foundations.Base
open Variadics _
open import Meta.Show
open import Meta.Effect hiding (_>>_) renaming (_>>=_ to _>>=ᵐ_)
open import Meta.Effect.Bind.State
open import Logic.Discreteness
open import System.Everything hiding (_<$>_)

open import Data.Unit
open import Data.Empty hiding (_≠_)
open import Data.Bool as Bool
open import Data.Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Any renaming (Any to Anyₘ ; any←map to any←mapₘ)
open import Data.Maybe.Correspondences.Unary.All renaming (All to Allₘ ; all-map to all-mapₘ ; all→map to all→mapₘ)
open import Data.Maybe.Instances.Bind.Properties
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Unary.Unique
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Correspondences.Binary.Suffix
open import Data.List.Operations.Properties as List
open import Data.List.Operations.Rel
open import Data.List.Operations.Discrete renaming (rem to remₗ)
open import Data.List.Instances.Map.Properties
open import Data.Sum
open import Data.String
open import Data.Fin.Inductive
open import Data.Fin.Inductive.Operations
open import Data.Fin.Inductive.Operations.Properties
open import Data.Vec.Inductive hiding (_++_) renaming (replicate to replicateᵥ)
open import Data.Vec.Inductive.Operations hiding (_++_ ; replicate) renaming (lookup to lookupᵥ)
open import Data.Vec.Inductive.Operations.Properties renaming (map-++ to map-++ᵥ)
open import Data.Vec.Inductive.Instances.Map

open import Order.Diagram.Meet
open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open decminmax ℕ-dec-total
open import Order.Constructions.Lex.Vec

open import Induction.Nat.Strong as Box using (□_)
open import Induction.Nat.VLex as Box∷× using (□∷×_)

open import Data.List.NonEmpty as List⁺

open import ListSet
open import KVMapU

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete as LFSet

open import ch2.Formula using (Var)
open import ch2.Sem
open import ch2.Appl
open import ch2.Ix.Formula
open import ch2.Ix.Lit
open import ch2.Ix.NF
open import ch2.Ix.CNF
open import ch2.Ix.DP
open import ch2.Ix.DPLL
open import ch2.Ix.DPTrail

private variable
  A : 𝒰
  v : Var
  Γ Δ Ξ : Ctx

-- iterative + backjumping + clause learning
-- aka CDCL

BJ-ty : {Γ : Ctx} → Lit Γ → ℕ → 𝒰
BJ-ty {Γ} p x =
    (tr : Trail Γ)
  → x ＝ length tr
  → p ∉ trail-lits tr
  → negate p ∉ trail-lits tr
  → Trail-Inv tr
  → Trail-Inv2 tr
  → Σ[ tr' ꞉ Trail Γ ] (Trail-Inv tr' × Trail-Inv2 tr' × Backjump-suffix tr tr')

backjump-loop-backtrack : {Γ : Ctx} → CNF Γ → (p : Lit Γ)
                        → ∀ {x}
                        → (□ BJ-ty p) x
                        → (tr : Trail Γ)
                        → x ＝ length tr
                        → p ∉ trail-lits tr
                        → negate p ∉ trail-lits tr
                        → Trail-Inv tr
                        → Trail-Inv2 tr

                        → (q : Lit Γ)
                        → (trr : Trail Γ)
                        → backtrack tr ＝ just (q , trr)

                        → Σ[ tr' ꞉ Trail Γ ] (Trail-Inv tr' × Trail-Inv2 tr' × Backjump-suffix tr tr')
backjump-loop-backtrack cls p {x} ih tr e p∉ np∉ ti ti2 q trr eb =
  let (cls' , tr' , ti' , ti2' , us') = unit-propagate-iter cls ((p , guessed) ∷ trr)
                                          (push-trailinv {tm = guessed} p∉r tir)
                                          (push-guessed-trailinv2 np∉r ti2r)
   in
  if List.has [] cls'
     then
       (let (  tr'
             , ti' , ti2' , ts') = Box.call ih prf
                                   trr
                                   refl p∉r np∉r tir ti2r
         in
          tr'
        , ti' , ti2'
        , bjsuffix-trans (bsuffix→bjsuffix bsf) ts')
     else
       tr , ti , ti2 , bjsuffix-refl
  where
  bsf : Backtrack-suffix tr (q , trr)
  bsf = backtrack-suffix-eq eb
  tr⊆ : trail-lits trr ⊆ trail-lits tr
  tr⊆ = map-⊆ fst (ope→subset $ suffix→ope $ suffix-uncons $ bsuffix→suffix bsf)
  p∉r : p ∉ trail-lits trr
  p∉r = contra tr⊆ p∉
  np∉r : negate p ∉ trail-lits trr
  np∉r = contra tr⊆ np∉
  tir : Trail-Inv trr
  tir = bsuffix-trailinv bsf ti
  ti2r : Trail-Inv2 trr
  ti2r = bsuffix-trailinv2 bsf ti ti2
  prf : length trr < x
  prf = <-≤-trans (<-≤-trans <-ascend
                             (suffix-length $ bsuffix→suffix bsf))
                  (=→≤ (e ⁻¹))

backjump-loop : {Γ : Ctx} → CNF Γ → (p : Lit Γ)
              → ∀[ □ BJ-ty p ⇒ BJ-ty p ]
backjump-loop {Γ} cls p {x} ih tr e p∉ np∉ ti ti2 =
  Maybe.elim (λ m → backtrack tr ＝ m
                  → Σ[ tr' ꞉ Trail Γ ] (Trail-Inv tr' × Trail-Inv2 tr' × Backjump-suffix tr tr'))
    (λ _ → tr , ti , ti2 , bjsuffix-refl)
    (λ where (q , trr) → backjump-loop-backtrack cls p ih tr e p∉ np∉ ti ti2 q trr)
    (backtrack tr) refl

backjump : CNF Γ
         → (p : Lit Γ)
         → (tr : Trail Γ)
         → p ∉ trail-lits tr
         → negate p ∉ trail-lits tr
         → Trail-Inv tr → Trail-Inv2 tr
         → Σ[ tr' ꞉ Trail Γ ] (Trail-Inv tr' × Trail-Inv2 tr' × Backjump-suffix tr tr')
backjump cls p tr p∉ np∉ ti ti2 =
  Box.fix (BJ-ty p) (backjump-loop cls p) tr refl p∉ np∉ ti ti2

DPLB-ty : {Γ : Ctx} → Vec ℕ (sizeₛ Γ) × ℕ → 𝒰
DPLB-ty {Γ} (x , y) =
    (cls : CNF Γ)
  → (tr : Trail Γ)
  → (ti : Trail-Inv tr)
  → (ti2 : Trail-Inv2 tr)
  → (rj : Rejstk Γ)
  → Rejstk-Inv rj tr
  → x ＝ map (λ q → 2 · sizeₛ Γ ∸ sizeₛ q) rj
  → y ＝ 2 · sizeₛ Γ ∸ length tr
  → Bool

dplb-loop-backjump : ∀ {x y}
                   → (□∷× DPLB-ty) (x , y)
                   → (cls : CNF Γ)
                   → (tr : Trail Γ)
                   → (ti : Trail-Inv tr)
                   → (ti2 : Trail-Inv2 tr)
                   → (rj : Rejstk Γ)
                   → Rejstk-Inv rj tr
                   → x ＝ map (λ q → 2 · sizeₛ Γ ∸ sizeₛ q) rj
                   → y ＝ 2 · sizeₛ Γ ∸ length tr

                   → (p : Lit Γ)
                   → (trr : Trail Γ)
                   → backtrack tr ＝ just (p , trr)

                   → Bool
dplb-loop-backjump {Γ} {x} {y} ih cls tr ti ti2 rj ri ex ey p trr eb =
  Box∷×.call ih
    prf
    -- computational args
    (conflict ∷ cls)
    ((negate p , deduced) ∷ tr')
    --
    (push-trailinv {tm = deduced} np∉' ti')
    (push-deduced-trailinv2 np∉' ti' ti2')
    (bump-at bfin p rj)
    (bump-rejstkinv-deduced {rj = rj}
       (bjsuffix-trans (bsuffix→bjsuffix bsf) ts')
       cg<
       ri)
    refl refl
  where
  bsf : Backtrack-suffix tr (p , trr)
  bsf = all-unjust (subst (λ q → Allₘ (Backtrack-suffix tr) q)
                          eb
                          (backtrack-suffix {tr = tr}))

  p∉ : p ∉ trail-lits trr
  p∉ = bsuffix→∉ ti bsf

  np∉ : negate p ∉ trail-lits trr
  np∉ = bsuffix→negate∉ ti ti2 bsf

  -- computational stuff
  trti' = backjump cls p trr
            p∉ np∉
            (bsuffix-trailinv bsf ti)
            (bsuffix-trailinv2 bsf ti ti2)
  tr' = trti' .fst
  ti' = trti' .snd .fst
  ti2' = trti' .snd .snd .fst
  ts' = trti' .snd .snd .snd

  declits = filter (is-guessed? ∘ snd) tr'
  conflict = insert-s (negate p) (image (negate ∘ fst) declits)
  --

  np∉' : negate p ∉ trail-lits tr'
  np∉' = contra (map-⊆ fst (ope→subset $ suffix→ope $ bjsuffix→suffix ts')) np∉

  cg< : count-guessed tr' < sizeₛ Γ
  cg< = <-≤-trans
          (≤-<-trans (ope-count (suffix→ope $ bjsuffix→suffix ts'))
                     (<≃suc≤ $ =→≤ (bsuffix→count-guessed bsf ⁻¹)))
          (count-guessed-size ti ti2)

  bfin : Fin (sizeₛ Γ)
  bfin = ℕ→fin (count-guessed tr') cg<

  p∉r : p ∉ lookupᵥ rj bfin
  p∉r = rejstkinv-∉ {rj = rj} bsf ts' cg< ti ti2 ri

  prf : (  map (λ q → 2 · sizeₛ Γ ∸ sizeₛ q)
               (bump-at bfin p rj)
         , 2 · sizeₛ Γ ∸ suc (length tr'))
          Box∷×.<∷× (x , y)
  prf =
    inl $
    subst (Vec-lex< _<_
                (mapᵥ (λ q → 2 · sizeₛ Γ ∸ sizeₛ q)
                      (bump-at bfin p rj)))
                (ex ⁻¹) $
    Vec-lex<-prefix-lup bfin
      (λ j jlt →
          lookup-map {xs = bump-at bfin p rj} j
        ∙ ap (λ q → 2 · sizeₛ Γ ∸ sizeₛ q)
             (lookup-tabulate j ∙ if-true (true→so! jlt))
        ∙ lookup-map {xs = rj} j ⁻¹) $
    ≤-<-trans (=→≤ (lookup-map {xs = bump-at bfin p rj} bfin)) $
    <-≤-trans
      (≤-<-trans
        (=→≤ (ap (λ q → 2 · sizeₛ Γ ∸ sizeₛ q)
                          (  lookup-tabulate bfin
                           ∙ if-false (false→so! (<-irr {n = fin→ℕ bfin}))
                           ∙ if-true (true→so! (the (fin→ℕ bfin ＝ fin→ℕ bfin) refl)))))
        (<-∸-2l-≃ {m = 2 · sizeₛ Γ} {n = sizeₛ (p ∷ lookupᵥ rj bfin)} {p = sizeₛ (lookupᵥ rj bfin)}
                           lit-set-size ⁻¹ $
         <-≤-trans <-ascend $
         =→≤ (  ap (suc ∘ sizeₛ)
                   (rem-∉-eq p∉r ⁻¹)
              ∙ size-∷ ⁻¹)))
      (=→≤ (lookup-map {xs = rj} bfin ⁻¹))

dplb-loop-guess : ∀ {x y}
                → (□∷× DPLB-ty) (x , y)
                → (cls : CNF Γ)
                → (tr : Trail Γ)
                → (ti : Trail-Inv tr)
                → (ti2 : Trail-Inv2 tr)
                → (rj : Rejstk Γ)
                → Rejstk-Inv rj tr
                → x ＝ map (λ q → 2 · sizeₛ Γ ∸ sizeₛ q) rj
                → y ＝ 2 · sizeₛ Γ ∸ length tr

                → (cls' : CNF Γ)
                → (tr'  : Trail Γ)
                → Trail-Inv tr'
                → Trail-Inv2 tr'
                → USP-suffix tr' tr
                → (ps : List (Lit Γ))
                → ps ≠ []
                → ps ＝ unassigned cls tr'

                → Bool
dplb-loop-guess {Γ} {x} {y} ih cls tr ti ti2 rj ri ex ey cls' tr' ti' ti2' us' ps ne eps =
  Box∷×.call ih
    prf
    -- computational args
    cls
    ((p , guessed) ∷ tr')
    --
    ti''
    (push-guessed-trailinv2 np∉ ti2')
    rj
    (push-rejstkinv-guessed {rj = rj} us' ri)
    refl refl
  where
  -- computational
  pp∈ : Σ[ l ꞉ Lit Γ ] (l ∈ ps)
  pp∈ = posneg-rule cls' ps ne
  p = pp∈ .fst
  --
  p∈ = pp∈ .snd
  pnp∉ : p ∉ trail-lits tr' × negate p ∉ trail-lits tr'
  pnp∉ = unassigned-∉ {c = cls} (subst (p ∈_) eps p∈)
  p∉ = pnp∉ .fst
  np∉ = pnp∉ .snd
  ti'' : Trail-Inv ((p , guessed) ∷ tr')
  ti'' = push-trailinv {tm = guessed} p∉ ti'
  prf : (  map (λ q → 2 · sizeₛ Γ ∸ sizeₛ q) rj
         , 2 · sizeₛ Γ ∸ suc (length tr'))
          Box∷×.<∷× (x , y)
  prf = inr (  ex ⁻¹
             , <-≤-trans
                  (<-∸-2l-≃ (trail-inv≤ {tr = (p , guessed) ∷ tr'}
                                        ti'') ⁻¹ $
                   ≤≃<suc $ (uspsuffix→len us'))
                  (=→≤ (ey ⁻¹)))

dplb-loop : ∀[ □∷× (DPLB-ty {Γ}) ⇒ DPLB-ty ]
dplb-loop {Γ} {x = x , y} ih cls tr ti ti2 rj ri ex ey =
  let (cls' , tr' , ti' , ti2' , us') = unit-propagate-iter cls tr ti ti2 in
  Dec.rec
    (λ _ → Maybe.elim (λ m → backtrack tr ＝ m → Bool)
              (λ _ → false)
              (λ where (p , trr) eb →
                          dplb-loop-backjump ih cls tr ti ti2 rj ri ex ey p trr eb)
              (backtrack tr) refl)
    (λ _ → let ps = unassigned cls tr' in
           Dec.rec (λ _ → true)
                   (λ ne → dplb-loop-guess ih cls  tr  ti  ti2  rj ri ex ey
                                              cls' tr' ti' ti2' us' ps ne refl)
                   (Dec-is-nil? {xs = ps}))
    ([] ∈? cls')

dplb : CNF Γ → Bool
dplb {Γ} c =
  Box∷×.fix∷× DPLB-ty
    dplb-loop
    c
    []
    (emp-trailinv {Γ = Γ}) emp-trailinv2
    (replicateᵥ (sizeₛ Γ) [])
    emp-rejstkinv
    refl
    refl

dplbsat : Formulaᵢ Γ → Bool
dplbsat = dplb ∘ snd ∘ defcnfs

dplbtaut : Formulaᵢ Γ → Bool
dplbtaut = not ∘ dplbsat ∘ Not

{-
main : Main
main =
  run $
  do -- put-str-ln $ "prime 11      : " ++ₛ (show $ tautology $ prime 11)
     -- put-str-ln $ "prime(DPLB) 13: " ++ₛ ppFBᵢ dplbtaut (prime 13)
     -- put-str-ln $ "prime(DPLB) 16: " ++ₛ ppFBᵢ dplbtaut (prime 16)
     put-str-ln $ "prime(DPLB) 21: " ++ₛ ppFBᵢ dplbtaut (prime 21)
-}
