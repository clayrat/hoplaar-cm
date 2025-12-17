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
                    → backtrack tr ＝ just (p , trr)

                    → Bool
dpli-loop-backtrack {Γ} {x} {y} ih tr ti ti2 rj ri ex ey p trr eb =
  Box∷×.call ih prf
    ((negate p , deduced) ∷ trr)
    ti'' ti2''
    (bump-at bfin p rj)
    ri''
    refl refl
  where
  bsf : Backtrack-suffix tr (p , trr)
  bsf = all-unjust (subst (λ q → Allₘ (Backtrack-suffix tr) q)
                          eb
                          (backtrack-suffix {tr = tr}))

  bcg : count-guessed tr ＝ suc (count-guessed trr)
  bcg = bsuffix→count-guessed bsf

  cg< : count-guessed trr < sizeₛ Γ
  cg< = <≃suc≤ $   =→≤ (bcg ⁻¹) ∙ count-guessed-size ti ti2

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

  ti'' : Trail-Inv ((negate p , deduced) ∷ trr)
  ti'' = contra (map-∈ _ unpack-inj)
                (λ np∈ → ti2 p (subst ((p , guessed) ∈_)
                                       etr
                                       (any-++-r (here refl)))
                                (subst (λ q → negate p ∈ₗ tail-of p (trail-lits q))
                                       etr $
                                 subst (λ q → negate p ∈ (tail-of p q))
                                       (trail-lits-++ {tr1 = pr} ⁻¹) $
                                 subst (negate p ∈_)
                                       (tail-of-++-r (λ p∈ → dtr (List.∈-map _ p∈)
                                                                 (here refl)) ⁻¹) $
                                 subst (negate p ∈_)
                                       (tail-of-∷ {z = p} ⁻¹)
                                       np∈))
         ∷ᵘ (snd $ uniq-uncons $ suffix-trailinv (bsuffix→suffix bsf) ti)

  ti2'' : Trail-Inv2 ((negate p , deduced) ∷ trr)
  ti2'' z z∈ =
    let z∈' = any-¬here (λ e → absurd (guessed≠deduced (ap snd e))) z∈ in
    contra (λ n∈ → subst (λ q → negate z ∈ tail-of z (trail-lits q))
                         etr $
                   subst (λ q → negate z ∈ tail-of z q)
                         (trail-lits-++ {tr1 = pr} ⁻¹) $
                   subst (negate z ∈_)
                         (tail-of-++-r {xs = trail-lits pr}
                                       (λ z∈ → dtr (List.∈-map _ z∈)
                                                   (List.∈-map _ $ there $ List.∈-map _ z∈')) ⁻¹) $
                   subst (negate z ∈_)
                         (tail-of-++-r {xs = p ∷ []}
                                       (¬any-∷ (contra (λ z=p → List.∈-map _ $
                                                                List.∈-map _ $
                                                                subst (λ q → (q , guessed) ∈ trr)
                                                                      z=p
                                                                      z∈')
                                                       (uniq-uncons uptr .fst))
                                               false!) ⁻¹) $
                   subst (negate z ∈_)
                         (tail-of-++-r {xs = negate p ∷ []}
                                       (¬any-∷ (contra (λ z=np → List.∈-map _ $
                                                                 List.∈-map _ $
                                                                 subst (λ q → (q , guessed) ∈ trr)
                                                                       z=np
                                                                       z∈')
                                                       (uniq-uncons ti'' .fst) )
                                               false!)) $
                   n∈) $
    ti2 z $
    subst ((z , guessed) ∈_)
          etr $
    any-++-r $
    there z∈'

  ri'' : Rejstk-Inv (bump-at bfin p rj) ((negate p , deduced) ∷ trr)
  ri'' x f x∈ =
    Dec.elim
      {C = λ q → x ∈ₛ (if ⌊ q ⌋
                         then lookupᵥ rj f
                         else if fin→ℕ f == fin→ℕ bfin
                                then p ∷ lookupᵥ rj f
                                else [])
               → negate x ∈ trail-lits (drop-guessed ((negate p , deduced) ∷ trr)
                                                     (count-guessed trr ∸ fin→ℕ f))}
      (λ lt x∈ →
           let lt' = <-≤-trans lt (=→≤ (ℕ→fin→ℕ _ cg<)) in
           subst (λ q → negate x ∈ trail-lits q)
                  (drop-guessed-++-l {pr = (negate p , deduced) ∷ []} {tr = trr} {n = count-guessed trr ∸ fin→ℕ f}
                     (id ∷ [])
                     (∸>0≃> ⁻¹ $ lt') ⁻¹) $
           subst (λ q → negate x ∈ trail-lits (Maybe.rec [] (λ ptr → drop-guessed (ptr .snd) (count-guessed trr ∸ fin→ℕ f)) q))
                 eb $
           subst (λ q → negate x ∈ trail-lits (drop-guessed tr q))
                     (ap (  _∸ fin→ℕ f) bcg
                          ∙ +∸-assoc 1 (count-guessed trr) (fin→ℕ f)
                              (<-weaken _ _ lt') ⁻¹) $
           ri x f x∈)
      (λ ge →
           Dec.elim
               {C = λ q → x ∈ₛ (if ⌊ q ⌋ then p ∷ lookupᵥ rj f else [])
                        → negate x ∈ trail-lits (drop-guessed ((negate p , deduced) ∷ trr)
                                                              (count-guessed trr ∸ fin→ℕ f))}
               (λ e →
                  let e' = e ∙ ℕ→fin→ℕ _ cg< in
                  [ (λ x=p →
                        subst (λ q → negate x ∈ trail-lits (drop-guessed ((negate p , deduced) ∷ trr) q))
                               (≤→∸=0 (=→≤ (e' ⁻¹)) ⁻¹) $
                        here (ap negate x=p))
                  , (λ x∈' →
                        subst (λ q → negate x ∈ trail-lits (drop-guessed ((negate p , deduced) ∷ trr) q))
                               (≤→∸=0 (=→≤ (e' ⁻¹)) ⁻¹) $
                        there $
                        subst (λ q → negate x ∈ trail-lits (Maybe.rec [] snd q))
                              eb $
                        subst (λ q → negate x ∈ trail-lits (drop-guessed tr q))
                              (ap (  _∸ fin→ℕ f) bcg
                                   ∙ +∸-assoc 1 (count-guessed trr) (fin→ℕ f)
                                       (=→≤ e') ⁻¹
                                   ∙ ap suc (≤→∸=0 (=→≤ (e' ⁻¹)))
                                   ∙ +-zero-r 1) $
                        ri x f x∈')
                  ]ᵤ ∘ ∈ₛ-∷→)
               (λ ne → false! ⦃ Refl-x∉ₛ[] ⦄)
               (ℕ-is-discrete {x = fin→ℕ f} {y = fin→ℕ bfin}))
      (<-dec {x = fin→ℕ f} {x = fin→ℕ bfin})
      (subst (x ∈_)
             (lookup-tabulate {f = bump-at-fun p rj (fin→ℕ bfin)} f)
             x∈)

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
                              (rem-∉-eq
                                 (λ p∈s →
                                     ti2 p
                                       (subst ((p , guessed) ∈_)
                                              etr
                                              (any-++-r (here refl)))
                                       (subst (λ q → negate p ∈ tail-of p (trail-lits q))
                                              etr $
                                        subst (λ q → negate p ∈ tail-of p q)
                                              (trail-lits-++ {tr1 = pr} ⁻¹) $
                                        subst (negate p ∈_)
                                              (tail-of-++-r (λ p∈ → dtr (List.∈-map _ p∈)
                                                            (here refl)) ⁻¹) $
                                        subst (negate p ∈_)
                                              (tail-of-∷ {z = p} ⁻¹) $
                                        subst (λ q → negate p ∈ trail-lits (Maybe.rec [] (λ ptr → ptr .snd) q))
                                               eb $
                                        subst (λ q → negate p ∈ trail-lits (drop-guessed tr q))
                                              (+-cancel-∸-r 1 (count-guessed trr)) $
                                        subst (λ q → negate p ∈ trail-lits (drop-guessed tr (q ∸ count-guessed trr)))
                                              bcg $
                                        subst (λ q → negate p ∈ trail-lits (drop-guessed tr (count-guessed tr ∸ q)))
                                              (ℕ→fin→ℕ (count-guessed trr) cg<) $
                                        ri p bfin p∈s)
                                        )
                                 ⁻¹)
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
    ((p , guessed) ∷ tr')
    ti''
    ti2''
    rj
    ri''
    refl refl
  where
  pp∈ : Σ[ l ꞉ Lit Γ ] (l ∈ ps)
  pp∈ = posneg-rule cls' ps ne
  p = pp∈ .fst
  p∈ = pp∈ .snd
  pnp∉ : p ∉ trail-lits tr' × negate p ∉ trail-lits tr'
  pnp∉ = unassigned-∉ {c = cls} (subst (p ∈_) eps p∈)
  p∉ = pnp∉ .fst
  np∉ = pnp∉ .snd
  ti'' : Trail-Inv ((p , guessed) ∷ tr')
  ti'' = contra (map-∈ _ unpack-inj) p∉ ∷ᵘ ti'
  ti2'' : Trail-Inv2 ((p , guessed) ∷ tr')
  ti2'' z z∈ =
    [ (λ z=p' → subst (λ q → negate z ∉ tail-of z (q ∷ trail-lits tr'))
                      (ap fst z=p') $
                subst (negate z ∉_)
                      (tail-of-∷ {z = z} {xs = trail-lits tr'} ⁻¹) $
                subst (λ q → negate q ∉ trail-lits tr')
                      (ap fst z=p' ⁻¹) $
                np∉)
    , (λ z∈' → subst (negate z ∉_)
                     (tail-of-++-r {xs = p ∷ []}
                                   (¬any-∷ (contra (λ z=p → List.∈-map _ $
                                                            List.∈-map _ $
                                                            subst (λ q → (q , guessed) ∈ tr')
                                                                  z=p
                                                                  z∈')
                                                   (uniq-uncons ti'' .fst))
                                           false!) ⁻¹) $
               ti2' z z∈')
   ]ᵤ (any-uncons z∈)
  ri'' : Rejstk-Inv rj ((p , guessed) ∷ tr')
  ri'' x f x∈ =
    let nx∈ = ri x f x∈ in
    Dec.rec
      (λ le →
          subst (λ q → negate x ∈ trail-lits (drop-guessed ((p , guessed) ∷ tr') q))
                (≤→∸=0 le ⁻¹) $
          there $
          subst (λ q → negate x ∈ trail-lits q)
                 (us' .snd .snd ⁻¹) $
          subst (negate x ∈_)
                (trail-lits-++ {tr1 = us' .fst} ⁻¹) $
          any-++-r {xs = trail-lits (us' .fst)} $
          subst (λ q → negate x ∈ trail-lits (drop-guessed tr q))
                (≤→∸=0 (=→≤ (uspsuffix→count-guessed us') ∙ ≤-ascend ∙ le)) $
          nx∈)
      (λ ge →
          let le' = ≤≃<suc ⁻¹ $ ≱→< ge in
          subst (λ q → negate x ∈ trail-lits (drop-guessed ((p , guessed) ∷ tr') q))
                (+∸-assoc _ _ _ le') $
          subst (λ q → negate x ∈ trail-lits (drop-guessed tr' (q ∸ fin→ℕ f)))
                (uspsuffix→count-guessed us') $
          subst (λ q → negate x ∈ trail-lits (drop-guessed q (count-guessed tr ∸ fin→ℕ f)))
                (us' .snd .snd ⁻¹) $
          [ (λ lt' →
                subst (λ q → negate x ∈ trail-lits q)
                      (drop-guessed-++-l
                         {pr = us' .fst} {n = count-guessed tr ∸ fin→ℕ f}
                         (us' .snd .fst)
                         (∸>0≃> ⁻¹ $ <-≤-trans lt' (=→≤ (uspsuffix→count-guessed us' ⁻¹)))
                         ⁻¹) $
                nx∈)
          , (λ e' →
               let e'' = ≤→∸=0 (=→≤ (uspsuffix→count-guessed us' ∙ e' ⁻¹)) in
               subst (λ q → negate x ∈ trail-lits (drop-guessed (us' .fst ++ tr) q))
                     (e'' ⁻¹) $
               subst (negate x ∈_)
                     (trail-lits-++ {tr1 = us' .fst} ⁻¹) $
               any-++-r {xs = trail-lits (us' .fst)} $
               subst (λ q → negate x ∈ trail-lits (drop-guessed tr q))
                     e'' $
               nx∈)
          ]ᵤ (≤→<⊎= le'))
      (≤-dec {x = suc (count-guessed tr')} {x = fin→ℕ f})
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
    then Maybe.elim (λ m → backtrack tr ＝ m → Bool)
           (λ _ → false)
           (λ where (p , trr) eb →
                       dpli-loop-backtrack ih tr ti ti2 rj ri ex ey p trr eb)
           (backtrack tr) refl
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

