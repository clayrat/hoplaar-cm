{-# OPTIONS --no-exact-split #-}
module ch2.Ix.DPLI where

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

DPLI-ty : {Γ : Ctx} → Vec ℕ (sizeₛ Γ) × ℕ → 𝒰
DPLI-ty {Γ} (x , y) =
    (tr : Trail Γ)
  → (ti : Trail-Inv tr)
  → (ti2 : Trail-Inv2 tr)
  → (rj : Rejstk Γ)
  → Rejstk-Inv rj tr
  → x ＝ map (λ q → 2 · sizeₛ Γ ∸ sizeₛ q) rj
  → y ＝ 2 · sizeₛ Γ ∸ length tr
  → Bool

dpli-loop-backtrack : ∀ {x y}
                    → (□∷× DPLI-ty) (x , y)
                    → (tr : Trail Γ)
                    → (ti : Trail-Inv tr)
                    → (ti2 : Trail-Inv2 tr)
                    → (rj : Rejstk Γ)
                    → Rejstk-Inv rj tr
                    → x ＝ map (λ q → 2 · sizeₛ Γ ∸ sizeₛ q) rj
                    → y ＝ 2 · sizeₛ Γ ∸ length tr

                    → (p : Lit Γ)
                    → (trr : Trail Γ)
                    → Backtrack-suffix tr (p , trr)

                    → Bool
dpli-loop-backtrack {Γ} {x} {y} ih tr ti ti2 rj ri ex ey p trr bsf =
  Box∷×.call ih prf
    -- computational arg
    ((negate p , deduced) ∷ trr)
    --
    (push-trailinv {tm = deduced} np∉ ti')
    (push-deduced-trailinv2 np∉ ti' (bsuffix-trailinv2 bsf ti ti2))
    (bump-at bfin p rj)
    (bump-rejstkinv-deduced {rj = rj} (bsuffix→bjsuffix bsf) cg< ri) -- TODO a version with Backtrack-suffix
    refl refl
  where
  np∉ : negate p ∉ trail-lits trr
  np∉ = bsuffix→negate∉ ti ti2 bsf

  bcg : count-guessed tr ＝ suc (count-guessed trr)
  bcg = bsuffix→count-guessed bsf

  cg< : count-guessed trr < sizeₛ Γ
  cg< = <≃suc≤ $ =→≤ (bcg ⁻¹) ∙ count-guessed-size ti ti2

  bfin : Fin (sizeₛ Γ)
  bfin = ℕ→fin (count-guessed trr) cg<

  pr = bsf .fst
  etr = bsf .snd .snd ⁻¹
  udptr :   Uniq (trail-pvars pr)
          × Uniq (trail-pvars ((p , guessed) ∷ trr))
          × (trail-pvars pr ∥ trail-pvars ((p , guessed) ∷ trr))
  udptr = ++→uniq {xs = trail-pvars pr}
                  (subst Uniq
                         (trail-pvars-++ {tr1 = pr}) $
                   subst (Uniq ∘ trail-pvars)
                         (etr ⁻¹)
                         ti)
  uptr = udptr .snd .fst
  dtr = udptr .snd .snd

  ti' = bsuffix-trailinv bsf ti

  p∉r : p ∉ lookupᵥ rj bfin
  p∉r = rejstkinv-∉ {rj = rj} {tr' = trr} bsf bjsuffix-refl cg< ti ti2 ri

  prf : (  map (λ q → 2 · sizeₛ Γ ∸ sizeₛ q)
                (bump-at bfin p rj)
         , 2 · sizeₛ Γ ∸ suc (length trr))
          Box∷×.<∷× (x , y)
  prf =
    (inl (subst (Vec-lex< _<_
                (mapᵥ (λ q → 2 · sizeₛ Γ ∸ sizeₛ q)
                      (bump-at bfin p rj)))
              (ex ⁻¹) $
        Vec-lex<-prefix-lup bfin
          (λ j jlt →
               lookup-map {xs = bump-at bfin p rj} j
             ∙ ap (λ q → 2 · sizeₛ Γ ∸ sizeₛ q)
                  (  lookup-tabulate j
                   ∙ if-true (true→so! jlt))
             ∙ lookup-map {xs = rj} j ⁻¹)
          (≤-<-trans
            (=→≤ (lookup-map {xs = bump-at bfin p rj} bfin))
            (<-≤-trans
               (≤-<-trans
                 (=→≤ (ap (λ q → 2 · sizeₛ Γ ∸ sizeₛ q)
                          (  lookup-tabulate bfin
                           ∙ if-false (false→so! (<-irr {n = fin→ℕ bfin}))
                           ∙ if-true (true→so! (the (fin→ℕ bfin ＝ fin→ℕ bfin) refl)))))
                 (<-∸-2l-≃ {m = 2 · sizeₛ Γ} {n = sizeₛ (p ∷ lookupᵥ rj bfin)} {p = sizeₛ (lookupᵥ rj bfin)}
                           lit-set-size ⁻¹ $
                 <-≤-trans <-ascend
                   (=→≤ (  ap (suc ∘ sizeₛ)
                              (rem-∉-eq p∉r ⁻¹)
                         ∙ size-∷ ⁻¹))))
               (=→≤ (lookup-map {xs = rj} bfin ⁻¹))))))

dpli-loop-guess : (cls : CNF Γ)
                → ∀ {x y}
                → (□∷× DPLI-ty) (x , y)
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
dpli-loop-guess {Γ} cls {x} {y} ih tr ti ti2 rj ri ex ey cls' tr' ti' ti2' us' ps ne eps =
  Box∷×.call ih prf
    -- computational arg
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

dpli-loop : CNF Γ → ∀[ □∷× (DPLI-ty {Γ}) ⇒ DPLI-ty ]
dpli-loop {Γ} cls {x = x , y} ih tr ti ti2 rj ri ex ey =
  let (cls' , tr' , ti' , ti2' , us') = unit-propagate-iter cls tr ti ti2 in
  if List.has [] cls'
    then Maybe.rec-with-∈
           (backtrack tr)
           (λ _ → false)
           (λ where (p , trr) mb →
                       dpli-loop-backtrack ih tr ti ti2 rj ri ex ey p trr
                                           (backtrack-suffix-∈ mb))
    else let ps = unassigned cls tr' in
         Dec.rec
           (λ _ → true)
           (λ ne → dpli-loop-guess cls ih tr  ti  ti2  rj ri ex ey
                                   cls'   tr' ti' ti2' us' ps ne refl)
           (Dec-is-nil? {xs = ps})

dpli : CNF Γ → Bool
dpli {Γ} c =
  Box∷×.fix∷× DPLI-ty
    (dpli-loop c)
    []
    (emp-trailinv {Γ = Γ})
    emp-trailinv2
    (replicateᵥ (sizeₛ Γ) [])
    emp-rejstkinv
    refl
    refl

dplisat : Formulaᵢ Γ → Bool
dplisat = dpli ∘ snd ∘ defcnfs

dplitaut : Formulaᵢ Γ → Bool
dplitaut = not ∘ dplisat ∘ Not

main : Main
main =
  run $
  do -- put-str-ln $ "prime 11      : " ++ₛ (show $ tautology $ prime 11)
     -- put-str-ln $ "prime(DPLI) 13: " ++ₛ ppFBᵢ dplitaut (prime 13)
     -- put-str-ln $ "prime(DPLI) 16: " ++ₛ ppFBᵢ dplitaut (prime 16)
     put-str-ln $ "prime(DPLI) 21: " ++ₛ ppFBᵢ dplitaut (prime 21)

