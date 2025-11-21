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

private variable
  A : 𝒰
  v : Var
  Γ Δ Ξ : Ctx

-- iterative + backjumping + clause learning
-- aka CDCL

-- TODO unify with DPLI

data Trailmix : 𝒰 where
  guessed deduced : Trailmix

tmxeq : Trailmix → Trailmix → Bool
tmxeq guessed guessed = true
tmxeq deduced deduced = true
tmxeq _ _ = false

is-guessed : Trailmix → 𝒰
is-guessed guessed = ⊤
is-guessed deduced = ⊥

is-guessed? : Trailmix → Bool
is-guessed? guessed = true
is-guessed? deduced = false

instance
  Reflects-is-guessed : ∀ {t} → Reflects (is-guessed t) (is-guessed? t)
  Reflects-is-guessed {t = guessed} = ofʸ tt
  Reflects-is-guessed {t = deduced} = ofⁿ id

guessed≠deduced : guessed ≠ deduced
guessed≠deduced p = subst is-guessed p tt

instance
  Reflects-Trailmix-Path : ∀ {t₁ t₂} → Reflects (t₁ ＝ t₂) (tmxeq t₁ t₂)
  Reflects-Trailmix-Path {(guessed)} {(guessed)} = ofʸ refl
  Reflects-Trailmix-Path {(guessed)} {(deduced)} = ofⁿ guessed≠deduced
  Reflects-Trailmix-Path {(deduced)} {(guessed)} = ofⁿ (guessed≠deduced ∘ _⁻¹)
  Reflects-Trailmix-Path {(deduced)} {(deduced)} = ofʸ refl

  Trailmix-is-discrete : is-discrete Trailmix
  Trailmix-is-discrete = reflects-path→is-discrete!

Trail : Ctx → 𝒰
Trail Γ = List (Lit Γ × Trailmix)

trail-lits : Trail Γ → List (Lit Γ)
trail-lits = map fst

trail-lits-++ : {tr1 tr2 : Trail Γ} → trail-lits (tr1 ++ tr2) ＝ trail-lits tr1 ++ trail-lits tr2
trail-lits-++ {tr1} {tr2} = map-++ fst tr1 tr2

trail-has : Trail Γ → Lit Γ → Bool
trail-has tr l = List.has l (trail-lits tr)

trail-pvars : Trail Γ → List (Var × Bool)
trail-pvars = map < unlit , positive > ∘ trail-lits

trail-pvars-++ : {tr1 tr2 : Trail Γ} → trail-pvars (tr1 ++ tr2) ＝ trail-pvars tr1 ++ trail-pvars tr2
trail-pvars-++ {tr1} {tr2} =
    ap (map < unlit , positive >) (trail-lits-++ {tr1 = tr1} {tr2 = tr2})
  ∙ map-++ < unlit , positive > (trail-lits tr1) (trail-lits tr2)

count-guessed : Trail Γ → ℕ
count-guessed = count (is-guessed? ∘ snd)

{-
-- TODO duplication but it's probably more hassle to fiddle with eliminators
trail-pvars⊆ : {tr : Trail Γ} → trail-pvars tr ⊆ polarize Γ
trail-pvars⊆ {Γ} {x = xl , false} x∈ =
  let (y , y∈ , ye) = List.map-∈Σ _ x∈ in
  ∈ₛ-∪∷←r {s₁ = mapₛ (_, true) Γ}
          (∈-mapₛ (subst (_∈ Γ) (ap fst ye ⁻¹) (unlit∈ y)))
trail-pvars⊆ {Γ} {x = xl , true}  x∈ =
  let (y , y∈ , ye) = List.map-∈Σ _ x∈ in
  ∈ₛ-∪∷←l (∈-mapₛ (subst (_∈ Γ) (ap fst ye ⁻¹) (unlit∈ y)))
-}

-- a proper trail mentions each literal once
Trail-Inv : Trail Γ → 𝒰
Trail-Inv = Uniq ∘ trail-pvars

emp-trailinv : Trail-Inv {Γ} []
emp-trailinv = []ᵘ

push-trailinv : {tr : Trail Γ} {p : Lit Γ} {tm : Trailmix}
              → p ∉ trail-lits tr
              → Trail-Inv tr
              → Trail-Inv ((p , tm) ∷ tr)
push-trailinv p∉ ti =
  contra (map-∈ _ unpack-inj) p∉ ∷ᵘ ti

prepend-trailinv : {tr tr' : Trail Γ}
                 → Trail-Inv tr'
                 → Trail-Inv tr
                 → trail-lits tr' ∥ trail-lits tr
                 → Trail-Inv (tr' ++ tr)
prepend-trailinv {tr} {tr'} ti' ti dj =
  subst Uniq
        (  map-++ < unlit , positive > (trail-lits tr') _ ⁻¹
         ∙ ap (map < unlit , positive >)
            (trail-lits-++ {tr1 = tr'}) ⁻¹) $
  uniq→++ ti' ti $
  ∥-map unpack-inj dj

opaque
  unfolding Suffix
  suffix-trailinv : {tr0 tr : Trail Γ}
                  → Suffix tr0 tr
                  → Trail-Inv tr
                  → Trail-Inv tr0
  suffix-trailinv (pr , e) ti =
    ++→uniq (subst Uniq (ap trail-pvars (e ⁻¹) ∙ trail-pvars-++ {tr1 = pr}) ti) .snd .fst

trail-inv≤ : {tr : Trail Γ} → Trail-Inv tr → length tr ≤ 2 · sizeₛ Γ
trail-inv≤ {Γ} {tr} ti =
    =→≤ (  map-length ⁻¹ ∙ map-length ⁻¹
         ∙ size-unique ti ⁻¹
         ∙ ap sizeₛ (from-list-map {xs = trail-lits tr}) ⁻¹
         ∙ size-map-inj unpack-inj)
  ∙ lit-set-size

backtrack : Trail Γ → Maybe (Lit Γ × Trail Γ)
backtrack []                   = nothing
backtrack ((_ , deduced) ∷ xs) = backtrack xs
backtrack ((p , guessed) ∷ xs) = just (p , xs)

All-deduced : Trail Γ → 𝒰
All-deduced tr = All (λ q → ¬ is-guessed (q. snd)) tr

backtrack-++-l : ∀ {pr tr : Trail Γ}
               → All-deduced pr
               → backtrack (pr ++ tr) ＝ backtrack tr
backtrack-++-l {pr = []}                  []     = refl
backtrack-++-l {pr = (l , guessed) ∷ pr} (d ∷ a) = absurd (d tt)
backtrack-++-l {pr = (l , deduced) ∷ pr} (d ∷ a) = backtrack-++-l a

Backtrack-suffix : Trail Γ → Lit Γ × Trail Γ → 𝒰
Backtrack-suffix {Γ} tr (p , tr′) =
  Σ[ pr ꞉ Trail Γ ] (  All-deduced pr
                     × (tr ＝ pr ++ (p , guessed) ∷ tr′))

opaque
  unfolding Suffix
  bsuffix→suffix : {tr tr' : Trail Γ} {p : Lit Γ}
                 → Backtrack-suffix {Γ} tr (p , tr')
                 → Suffix ((p , guessed) ∷ tr') tr
  bsuffix→suffix (pr , _ , e) = (pr , e ⁻¹)

-- TODO Σ-reflects?
backtrack-suffix : {tr : Trail Γ} → Allₘ (Backtrack-suffix tr) (backtrack tr)
backtrack-suffix {tr = []}                 = nothing
backtrack-suffix {tr = (p , guessed) ∷ tr} =
  just ([] , [] , refl)
backtrack-suffix {tr = (p , deduced) ∷ tr} =
  all-mapₘ (λ where (pr , apr , e) →
                      ( (p , deduced) ∷ pr)
                      , id ∷ apr
                      , ap ((p , deduced) ∷_) e) $
  backtrack-suffix {tr = tr}

-- TODO use maybe membership everywhere
backtrack-suffix-eq : {tr tr' : Trail Γ} {p : Lit Γ}
                    → backtrack tr ＝ just (p , tr')
                    → Backtrack-suffix tr (p , tr')
backtrack-suffix-eq {tr} eb =
  all-unjust $
  subst (λ q → Allₘ (Backtrack-suffix tr) q)
        eb $
  backtrack-suffix {tr = tr}

eq-backtrack-suffix : {tr tr' : Trail Γ} {p : Lit Γ}
                    → Backtrack-suffix tr (p , tr')
                    → backtrack tr ＝ just (p , tr')
eq-backtrack-suffix (pr , a , e) = ap backtrack e ∙ backtrack-++-l a

bnone→count-guessed : {tr : Trail Γ}
                    → backtrack tr ＝ nothing
                    → count-guessed tr ＝ 0
bnone→count-guessed {tr = []}                 _ = refl
bnone→count-guessed {tr = (l , guessed) ∷ tr} e = false! e
bnone→count-guessed {tr = (l , deduced) ∷ tr} e = bnone→count-guessed {tr = tr} e

bsuffix→∉ : {tr tr' : Trail Γ} {p : Lit Γ}
          → Trail-Inv tr
          → Backtrack-suffix {Γ} tr (p , tr')
          → p ∉ trail-lits tr'
bsuffix→∉ {tr'} {p} ti bsf p∈ =
  ++→uniq
     (subst Uniq
            (  ap (map < unlit , positive >)
                  (  ap trail-lits
                        (bsf .snd .snd ∙ ++-assoc (bsf .fst) (_ ∷ []) tr'  ⁻¹)
                   ∙ trail-lits-++ {tr1 = bsf .fst ++ _ ∷ []})
             ∙ map-++ < unlit , positive > (trail-lits (bsf .fst ++ _ ∷ [])) (trail-lits tr')
             ∙ ap (_++ trail-pvars tr')
                  (  ap (map < unlit , positive >) (map-++ fst (bsf .fst) ((p , guessed) ∷ []))
                   ∙ map-++ < unlit , positive > (trail-lits (bsf .fst)) (p ∷ [])))
            ti)
     .snd .snd
     (any-++-r (here refl))
     (List.∈-map (< unlit , positive >) p∈)

bsuffix→count-guessed : {tr tr' : Trail Γ} {p : Lit Γ}
                      → Backtrack-suffix tr (p , tr')
                      → count-guessed tr ＝ suc (count-guessed tr')
bsuffix→count-guessed {tr'} (pr , apr , e) =
    ap count-guessed e
  ∙ count-++ _ pr _
  ∙ ap (_+ (suc (count-guessed tr')))
       (none→count _ pr (all-map (not-so ∘ contra (so→true! ⦃ Reflects-is-guessed ⦄)) apr))

bsuffix-trailinv : {tr tr' : Trail Γ} {p : Lit Γ}
                 → Backtrack-suffix {Γ} tr (p , tr')
                 → Trail-Inv tr
                 → Trail-Inv tr'
bsuffix-trailinv bsf = snd ∘ uniq-uncons ∘ suffix-trailinv (bsuffix→suffix bsf)

unassigned : CNF Γ → Trail Γ → List (Lit Γ)
unassigned cls trail =
  subtract
    (unions (image (image abs) cls))
    (image (abs ∘ fst) trail)

unassigned-∉ : {c : CNF Γ} {tr : Trail Γ} {l : Lit Γ}
             → l ∈ unassigned c tr
             → l ∉ trail-lits tr × negate l ∉ trail-lits tr
unassigned-∉ {c} {tr} {l} l∈u =
  let (l∈u , l∉ta) = subtract-∈ l∈u
      (ls , ls∈ , l∈′) = unions-∈ l∈u
      (zs , zs∈ , lse) = image-∈Σ {xs = c} ls∈
      (q , q∈ , zse) = image-∈Σ {xs = zs} (subst (l ∈_) lse l∈′)
    in
    (λ l∈t → l∉ta $
             ⊆-nub {R = λ _ _ → Reflects-lit Reflects-String-Path} $
             subst (_∈ map (abs ∘ fst) tr) (abs-idem ∙ zse ⁻¹) $
             subst (abs (abs q) ∈_) (happly map-pres-comp tr ⁻¹) $
             List.∈-map _ $
             subst (_∈ trail-lits tr) zse l∈t)
  , (λ nl∈t → l∉ta $
              ⊆-nub {R = λ _ _ → Reflects-lit Reflects-String-Path} $
              subst (_∈ map (abs ∘ fst) tr) (abs-negate ∙ abs-idem ∙ zse ⁻¹) $
              subst (abs (negate (abs q)) ∈_) (happly map-pres-comp tr ⁻¹) $
              List.∈-map abs $
              subst (λ q → negate q ∈ trail-lits tr) zse nl∈t)

-- TODO I'll drop the lookup structure as our kvmaps are lists internally anyway
-- and it's a hassle to keep it in sync with the trail

is-fresh-unit-clause : Trail Γ → Clause Γ → Bool
is-fresh-unit-clause tr []          = false
is-fresh-unit-clause tr (l ∷ [])    = not (trail-has tr l)
is-fresh-unit-clause tr (_ ∷ _ ∷ _) = false

fresh-unit-clause-prop : {tr : Trail Γ} {c : Clause Γ}
                       → ⌞ is-fresh-unit-clause tr c ⌟
                       → Σ[ l ꞉ Lit Γ ] (c ＝ l ∷ []) × (l ∉ trail-lits tr)
fresh-unit-clause-prop {tr} {c = l ∷ []} ifuc =
  l , refl , so→false! ifuc

tail-of : Lit Γ → List (Lit Γ) → List (Lit Γ)
tail-of x ls = List.tail (span (λ q → not (Lit-= _=?_ q x)) ls .snd)

tail-of-∷ : {z : Lit Γ} {xs : List (Lit Γ)}
          → tail-of z (z ∷ xs) ＝ xs
tail-of-∷ {z} =
  ap (λ q → List.tail (q .snd))
     (if-false $
      subst So (not-invol _ ⁻¹) $
      true→so! ⦃ Reflects-lit Reflects-String-Path {lx = z} ⦄ refl)

tail-of-++-r : {z : Lit Γ} {xs ys : List (Lit Γ)}
             → z ∉ xs → tail-of z (xs ++ ys) ＝ tail-of z ys
tail-of-++-r {z} {xs} z∉ =
  ap (λ q → List.tail (q .snd))
     (span-++-r xs $
      all-map (λ {x} →
                    not-so
                  ∘ contra (  _⁻¹
                            ∘ so→true! ⦃ Reflects-lit Reflects-String-Path {lx = x} ⦄)) $
      ¬Any→All¬ z∉)

{-
opaque
  unfolding Suffix
  tail-of-suffix : {xs ys : List (Lit Γ)}
                 → Suffix xs ys
                 → ∀ {z} → tail-of z xs ⊆ tail-of z ys
  tail-of-suffix  (txy , exy)         = {!!}
-}

tail-of-bsuffix : {tr tr' : Trail Γ} {p : Lit Γ}
                → Trail-Inv tr
                → Backtrack-suffix {Γ} tr (p , tr')
                → tail-of p (trail-lits tr) ＝ trail-lits tr'
tail-of-bsuffix {tr'} {p} ti (pr , ad , e) =
    ap (tail-of p) (ap trail-lits e ∙ trail-lits-++ {tr1 = pr})
  ∙ tail-of-++-r {z = p} {xs = trail-lits pr} {ys = p ∷ trail-lits tr'}
                 (λ p∈ →
                      let (_ , _ , dj) = ++→uniq {xs = trail-pvars pr}
                                                 (subst Uniq
                                                        (  ap trail-pvars e
                                                         ∙ trail-pvars-++ {tr1 = pr})
                                                        ti) in
                      dj (List.∈-map < unlit , positive > p∈) (here refl))
  ∙ tail-of-∷ {z = p}

-- a proper trail only guesses each variable once
Trail-Inv2 : Trail Γ → 𝒰
Trail-Inv2 tr =
  ∀ x → (x , guessed) ∈ tr
      → negate x ∉ tail-of x (trail-lits tr)

emp-trailinv2 : Trail-Inv2 {Γ = Γ} []
emp-trailinv2 x = false!

bsuffix→negate∉ : {tr tr' : Trail Γ} {p : Lit Γ}
                → Trail-Inv tr
                → Trail-Inv2 tr
                → Backtrack-suffix {Γ} tr (p , tr')
                → negate p ∉ trail-lits tr'
bsuffix→negate∉ {tr} {tr'} {p} ti ti2 bsf =
  subst (negate p ∉_)
         (  ap (λ q → tail-of p q) etr
          ∙ tail-of-++-r (λ p∈' →
                           ++→uniq
                             (subst Uniq
                                    (  ap (map < unlit , positive >) etr
                                     ∙ map-++ < unlit , positive > (trail-lits (bsf .fst)) (p ∷ trail-lits tr'))
                                    ti)
                             .snd .snd
                             (List.∈-map (< unlit , positive >) p∈')
                             (here refl))
          ∙ tail-of-∷ {z = p}) $
  ti2 p $
  subst ((p , guessed) ∈_)
         (bsf .snd .snd ⁻¹) $
  any-++-r (here refl)
  where
  etr : trail-lits tr ＝ trail-lits (bsf .fst) ++ p ∷ trail-lits tr'
  etr =   ap trail-lits (bsf .snd .snd)
        ∙ trail-lits-++ {tr1 = bsf .fst}


-- TODO try proving via ≟
push-deduced-trailinv2 : {tr : Trail Γ} {p : Lit Γ}
                       → p ∉ trail-lits tr
                       → Trail-Inv tr
                       → Trail-Inv2 tr
                       → Trail-Inv2 ((p , deduced) ∷ tr)
push-deduced-trailinv2 {tr} {p} p∉ ti ti2 z z∈ =
  let z∈' = any-¬here (λ e → absurd (guessed≠deduced (ap snd e))) z∈ in
  contra (subst (negate z ∈_)
                (tail-of-++-r $
                 ¬any-∷ (λ z=np →
                           uniq-uncons (push-trailinv {tm = deduced} p∉ ti) .fst $
                           List.∈-map < unlit , positive > $
                           List.∈-map fst $
                           subst (λ q → (q , guessed) ∈ tr) z=np z∈')
                        false!)) $
  ti2 z z∈'

prepend-deduced-trailinv2 : {tr tr' : Trail Γ}
                          → All-deduced tr'
                          → Trail-Inv tr'
                          → Trail-Inv tr
                          → trail-lits tr' ∥ trail-lits tr
                          → Trail-Inv2 tr
                          → Trail-Inv2 (tr' ++ tr)
prepend-deduced-trailinv2 {tr} {tr'} ad ti' ti dj ti2 x x∈ =
  subst (λ q → negate x ∉ tail-of x q)
        (trail-lits-++ {tr1 = tr'} {tr2 = tr} ⁻¹) $
  [ (λ am → absurd (List.All→∀∈ ad (x , guessed) am tt))
  , (λ x∈' →
        subst (negate x ∉_)
              (tail-of-++-r
                 (λ x∈m → ++→uniq (subst Uniq
                                         (trail-pvars-++ {tr1 = tr'} {tr2 = tr})
                                         (prepend-trailinv ti' ti dj))
                            .snd .snd
                            (List.∈-map _ x∈m)
                            (List.∈-map _ (List.∈-map _ x∈'))) ⁻¹) $
        ti2 x x∈')
   ]ᵤ (any-split x∈)

push-guessed-trailinv2 : {tr : Trail Γ} {p : Lit Γ}
                       → negate p ∉ trail-lits tr
                       → Trail-Inv2 tr
                       → Trail-Inv2 ((p , guessed) ∷ tr)
push-guessed-trailinv2 {tr} {p} np∉ ti2 z z∈ =
  Dec.rec
    (λ z=p →
         subst (λ q → negate z ∉ tail-of z (q ∷ trail-lits tr))
               z=p $
         subst (negate z ∉_)
               (tail-of-∷ {z = z} {xs = trail-lits tr} ⁻¹) $
         subst (λ q → negate q ∉ trail-lits tr)
               (z=p ⁻¹) $
         np∉)
    (λ z≠p →
         contra (subst (negate z ∈_)
                       (tail-of-++-r {xs = p ∷ []}
                                     (¬any-∷ z≠p false!))) $
         ti2 z $
         any-¬here (contra (ap fst) z≠p) z∈)
    (z ≟ p)

bsuffix-trailinv2 : {tr tr' : Trail Γ} {p : Lit Γ}
                  → Backtrack-suffix {Γ} tr (p , tr')
                  → Trail-Inv tr
                  → Trail-Inv2 tr
                  → Trail-Inv2 tr'
bsuffix-trailinv2 {tr} {tr'} {p} bsf ti ti2 z z∈ =
  contra (λ nz∈ → subst (λ q → negate z ∈ tail-of z q)
                        (etr ⁻¹) $
                  subst (λ q → negate z ∈ q)
                        (tail-of-++-r {z = z} {xs = trail-lits (bsf .fst ++ _ ∷ [])}
                                      (λ z∈' → ++→uniq
                                                 (subst Uniq (  ap (map < unlit , positive >) etr
                                                              ∙ map-++ < unlit , positive > (trail-lits (bsf .fst ++ _ ∷ [])) (trail-lits tr')
                                                              ∙ ap (map < unlit , positive > (trail-lits (bsf .fst ++ (p , guessed) ∷ [])) ++_)
                                                                   (happly (map-pres-comp ⁻¹) tr'))
                                                        ti)
                                                 .snd .snd
                                                 (List.∈-map (< unlit , positive >) z∈')
                                                 (List.∈-map (< unlit , positive > ∘ fst) z∈)) ⁻¹)
                  nz∈) $
  ti2 z $
  subst ((z , guessed) ∈_)
        (bsf .snd .snd ⁻¹) $
  any-++-r $
  there z∈
  where
  etr : trail-lits tr ＝ trail-lits (bsf .fst ++ (p , guessed) ∷ []) ++ trail-lits tr'
  etr =   ap trail-lits
             (bsf .snd .snd ∙ ++-assoc (bsf .fst) (_ ∷ []) tr' ⁻¹)
        ∙ trail-lits-++ {tr1 = bsf .fst ++ _ ∷ []}

guessed-vars : Trail Γ → List Var
guessed-vars = map unlit ∘ trail-lits ∘ filter (is-guessed? ∘ snd)

-- TODO should this be Inv2 instead?
-- TODO copypaste
uniq-guessed : {tr : Trail Γ}
             → Trail-Inv tr → Trail-Inv2 tr
             → Uniq (guessed-vars tr)
uniq-guessed {tr = []}                  ti1        ti2 = []ᵘ
uniq-guessed {tr = (x , guessed) ∷ tr} (ni ∷ᵘ ti1) ti2 =
  contra (λ x∈ → let (y , y∈ , ye) = List.map-∈Σ unlit x∈
                     ((z , ztr) , z∈ , ze) = List.map-∈Σ fst y∈
                   in
                 [ (λ y=x → List.∈-map _ $
                            subst (_∈ map fst tr) (ze ⁻¹ ∙ y=x) $
                            List.∈-map _ $
                            ope→subset filter-OPE z∈)
                 , (λ y=nx → absurd (ti2 x (here refl) $
                                     subst (negate x ∈_)
                                           (tail-of-∷ {z = x} {xs = trail-lits tr} ⁻¹) $
                                     subst (_∈ trail-lits tr)
                                           (ze ⁻¹ ∙ y=nx) $
                                     List.∈-map _ $
                                     ope→subset filter-OPE z∈))
                 ]ᵤ (unlit-eq {x = y} {y = x} (ye ⁻¹)))
         ni ∷ᵘ uniq-guessed ti1
                  λ z z∈ →
                     subst (negate z ∉_)
                           (tail-of-++-r
                              (¬any-∷
                                 (contra (λ z=x → List.∈-map _ $
                                                  List.∈-map _ $
                                                  subst (λ q → (q , guessed) ∈ tr) z=x z∈)
                                         ni)
                                 false!)) $
                     ti2 z (there z∈)
uniq-guessed {tr = (x , deduced) ∷ tr} (ni ∷ᵘ ti1)  ti2 =
  uniq-guessed ti1
    λ z z∈ →
       subst (negate z ∉_)
             (tail-of-++-r
                (¬any-∷
                   (contra (λ z=x → List.∈-map _ $
                                    List.∈-map _ $
                                    subst (λ q → (q , guessed) ∈ tr) z=x z∈)
                           ni)
                   false!)) $
       ti2 z (there z∈)

count-guessed-size : {tr : Trail Γ}
                   → Trail-Inv tr → Trail-Inv2 tr
                   → count-guessed tr ≤ sizeₛ Γ
count-guessed-size {Γ} {tr} ti1 ti2 =
    =→≤ (  length-filter _ tr ⁻¹
         ∙ map-length {f = fst} ⁻¹
         ∙ map-length {f = unlit} ⁻¹
         ∙ size-unique (uniq-guessed ti1 ti2) ⁻¹)
  ∙ size-⊆ λ x∈ →
              let x∈' = list-∈ {xs = guessed-vars tr} x∈
                  (y , y∈ , ye) = List.map-∈Σ unlit x∈'
                in
              subst (_∈ Γ) (ye ⁻¹) (unlit∈ y)

USP-suffix : Trail Γ → Trail Γ → 𝒰
USP-suffix {Γ} tr' tr =
  Σ[ pr ꞉ Trail Γ ] (  All-deduced pr
                     × (tr' ＝ pr ++ tr))

uspsuffix→len : {tr tr' : Trail Γ}
              → USP-suffix tr' tr
              → length tr ≤ length tr'
uspsuffix→len {tr} (pr , a , e) =
    ≤-+-l
  ∙ =→≤ (  ++-length pr tr ⁻¹
         ∙ ap length (e ⁻¹) )

uspsuffix→count-guessed : {tr tr' : Trail Γ}
                        → USP-suffix tr' tr
                        → count-guessed tr ＝ count-guessed tr'
uspsuffix→count-guessed {tr} (pr , a , e) =
    ap (_+ count-guessed tr)
       (none→count _ pr
          (all-map false→so! a) ⁻¹)
  ∙ count-++ _ pr tr ⁻¹
  ∙ ap count-guessed (e ⁻¹)

Rejstk : Ctx → 𝒰
Rejstk Γ = Vec (LFSet (Lit Γ)) (sizeₛ Γ)

-- iterated backtrack
drop-guessed : Trail Γ → ℕ → Trail Γ
drop-guessed tr  0      = tr
drop-guessed tr (suc n) =
  Maybe.rec
    []
    (λ ptr → drop-guessed (ptr .snd) n)
    (backtrack tr)

drop-guessed-[] : ∀ {n}
                → drop-guessed (the (Trail Γ) []) n ＝ []
drop-guessed-[] {n = zero}  = refl
drop-guessed-[] {n = suc n} = refl

drop-guessed-+ : ∀ {n m} {tr : Trail Γ}
               → drop-guessed (drop-guessed tr n) m ＝ drop-guessed tr (n + m)
drop-guessed-+ {n = zero}           = refl
drop-guessed-+ {n = suc n} {m} {tr} with backtrack tr | recall backtrack tr
... | just (p , tr0) | ⟪ eq ⟫ =
  drop-guessed-+ {n = n}
... | nothing        | _      =
  drop-guessed-[] {n = m}

drop-guessed-++-l : ∀ {pr tr : Trail Γ} {n}
                  → All-deduced pr
                  → 0 < n
                  → drop-guessed (pr ++ tr) n ＝ drop-guessed tr n
drop-guessed-++-l {n = zero} a nz = false! nz
drop-guessed-++-l {n = suc n} a _ = ap (Maybe.rec [] (λ ptr → drop-guessed (ptr .snd) n)) (backtrack-++-l a)

drop-guessed-suffix : ∀ {tr : Trail Γ} {n}
                    → Suffix (drop-guessed tr n) tr
drop-guessed-suffix      {n = zero}  =
  suffix-refl
drop-guessed-suffix {tr} {n = suc n} with backtrack tr | recall backtrack tr
... | just (p , tr0) | ⟪ eq ⟫ =
  suffix-trans
    (drop-guessed-suffix {n = n})
    (suffix-uncons $ bsuffix→suffix $ backtrack-suffix-eq {tr = tr} eq)
... | nothing        | ⟪ eq ⟫ =
  []-suffix

cg-drop-guessed : ∀ {n} {tr : Trail Γ}
                → count-guessed (drop-guessed tr n) ＝ count-guessed tr ∸ n
cg-drop-guessed {n = zero}       = refl
cg-drop-guessed {n = suc n} {tr} with backtrack tr | recall backtrack tr
... | just (p , tr0) | ⟪ eq ⟫ =
    cg-drop-guessed {n = n}
  ∙ ap (_∸ suc n)
       (bsuffix→count-guessed $ backtrack-suffix-eq {tr = tr} eq) ⁻¹
... | nothing        | ⟪ eq ⟫ =
  ap (_∸ suc n)
     (bnone→count-guessed {tr = tr} eq) ⁻¹

bsuffix-drop-guessed : {tr tr' : Trail Γ} {p : Lit Γ} {n : ℕ}
                     → Backtrack-suffix {Γ} tr (p , tr')
                     → drop-guessed tr (suc n) ＝ drop-guessed tr' n
bsuffix-drop-guessed {n} bsf =
  ap (Maybe.rec [] (λ ptr → drop-guessed (ptr .snd) n)) (eq-backtrack-suffix bsf)

-- add literal to a set at given depth, empty out trailing sets
bump-at-fun : ∀ {n} → Lit Γ → Vec (LFSet (Lit Γ)) n → ℕ → Fin n → LFSet (Lit Γ)
bump-at-fun l r k f =
  if fin→ℕ f <? k
    then lookupᵥ r f
    else if fin→ℕ f == k
           then l ∷ lookupᵥ r f
           else []

bump-at : Fin (sizeₛ Γ) → Lit Γ → Rejstk Γ → Rejstk Γ
bump-at f l r =
  tabulate (bump-at-fun l r (fin→ℕ f))

Rejstk-Inv : Rejstk Γ → Trail Γ → 𝒰
Rejstk-Inv {Γ} rj tr =
  ∀ x (f : Fin (sizeₛ Γ))
      → x ∈ lookupᵥ rj f
      → negate x ∈ (trail-lits $ drop-guessed tr (count-guessed tr ∸ fin→ℕ f))

emp-rejstkinv : Rejstk-Inv (replicateᵥ (sizeₛ Γ) []) []
emp-rejstkinv x f x∈ =
  false! ⦃ Refl-x∉ₛ[] ⦄ $
  subst (x ∈ₛ_) (lookup-replicate f) x∈

-- backjumping

Backjump-suffix : Trail Γ → Trail Γ → 𝒰
Backjump-suffix {Γ} tr tr′ =
  tr′ ＝ drop-guessed tr (count-guessed tr ∸ count-guessed tr′)

bjsuffix-cg : {tr tr' : Trail Γ}
            → Backjump-suffix tr tr'
            → count-guessed tr' ≤ count-guessed tr
bjsuffix-cg {tr} {tr'} e =
    =→≤ (ap count-guessed e ∙ cg-drop-guessed {n = count-guessed tr ∸ count-guessed tr'} {tr = tr})
  ∙ (∸≤≃≤+ {m = count-guessed tr} {n = count-guessed tr ∸ count-guessed tr'} ⁻¹ $ ≤-+-l)

bjsuffix-refl : {tr : Trail Γ} → Backjump-suffix tr tr
bjsuffix-refl {tr} = ap (drop-guessed tr) (∸-cancel (count-guessed tr) ⁻¹)

bjsuffix-trans : {tr tr' tr'' : Trail Γ}
               → Backjump-suffix tr tr' → Backjump-suffix tr' tr'' → Backjump-suffix tr tr''
bjsuffix-trans {tr} {tr'} {tr''} e e' =
    e'
  ∙ ap (λ q → drop-guessed q (count-guessed tr' ∸ count-guessed tr''))
       e
  ∙ drop-guessed-+ {n = count-guessed tr ∸ count-guessed tr'}
                   {m = count-guessed tr' ∸ count-guessed tr''}
                   {tr = tr}
  ∙ ap (drop-guessed tr)
       (  +∸-assoc (count-guessed tr ∸ count-guessed tr') (count-guessed tr') (count-guessed tr'')
                   (bjsuffix-cg e')
        ∙ ap (_∸ count-guessed tr'')
             (∸+=id (count-guessed tr') (count-guessed tr)
                    (bjsuffix-cg e)))

bsuffix→bjsuffix : ∀ {tr tr' : Trail Γ} {p}
                → Backtrack-suffix tr (p , tr')
                → Backjump-suffix tr tr'
bsuffix→bjsuffix {tr} {tr'} bs =
    ap (Maybe.rec [] (λ ptr → ptr .snd))
       (eq-backtrack-suffix bs ⁻¹)
  ∙ ap (drop-guessed tr)
       (+-cancel-∸-r 1 (count-guessed tr') ⁻¹)
  ∙ ap (λ q → drop-guessed tr (q ∸ count-guessed tr'))
       (bsuffix→count-guessed bs ⁻¹)

bjsuffix→suffix : {tr tr' : Trail Γ}
                → Backjump-suffix tr tr'
                → Suffix tr' tr
bjsuffix→suffix {tr} {tr'} bjs =
  suffix-trans
    (=→suffix bjs)
    (drop-guessed-suffix {n = count-guessed tr ∸ count-guessed tr'})

-- TODO these 3 are adhoc/messy
rejstkinv-∉ : {rj : Rejstk Γ} {tr tr0 tr' : Trail Γ} {p : Lit Γ}
            → Backtrack-suffix tr (p , tr0)
            → Backjump-suffix tr0 tr'
            → (cg< : count-guessed tr' < sizeₛ Γ)
            → Trail-Inv tr → Trail-Inv2 tr
            → Rejstk-Inv rj tr
            → p ∉ lookupᵥ rj (ℕ→fin (count-guessed tr') cg<)
rejstkinv-∉ {tr} {tr0} {tr'} {p} bsf bjsf cg< ti ti2 ri p∈ =
  ti2 p
      (subst ((p , guessed) ∈_)
             (bsf .snd .snd ⁻¹) $
       any-++-r (here refl)) $
  subst (λ q → negate p ∈ tail-of p q)
        (etr ⁻¹) $
  subst (negate p ∈_)
        -- TODO copypaste
        (tail-of-++-r (λ p∈' →
                           ++→uniq
                             (subst Uniq
                                    (  ap (map < unlit , positive >) etr
                                     ∙ map-++ < unlit , positive > (trail-lits (bsf .fst)) (p ∷ trail-lits tr0))
                                    ti)
                             .snd .snd
                             (List.∈-map (< unlit , positive >) p∈')
                             (here refl)) ⁻¹) $
  subst (negate p ∈_)
        (tail-of-∷ {z = p} ⁻¹) $
  map-⊆ fst (ope→subset $ suffix→ope $ bjsuffix→suffix bjsf) $
  subst (λ q → negate p ∈ trail-lits q)
        (bjsf ⁻¹) $
  subst (λ q → negate p ∈ trail-lits q)
        (bsuffix-drop-guessed {n = count-guessed tr0 ∸ count-guessed tr'} bsf) $
  subst (λ q → negate p ∈ trail-lits (drop-guessed tr q))
        (+∸-assoc 1 (count-guessed tr0) (count-guessed tr')
                    (bjsuffix-cg bjsf) ⁻¹) $
  subst (λ q → negate p ∈ trail-lits (drop-guessed tr (q ∸ count-guessed tr')))
        (bsuffix→count-guessed bsf) $
  subst (λ q → negate p ∈ trail-lits (drop-guessed tr (count-guessed tr ∸ q)))
        (ℕ→fin→ℕ (count-guessed tr') cg<) $
        ri p (ℕ→fin (count-guessed tr') cg<) p∈
  where
  -- TODO copypaste from bsuffix→negate∉
  etr : trail-lits tr ＝ trail-lits (bsf .fst) ++ p ∷ trail-lits tr0
  etr =   ap trail-lits (bsf .snd .snd)
        ∙ trail-lits-++ {tr1 = bsf .fst}

bump-rejstkinv-deduced : {rj : Rejstk Γ} {tr tr' : Trail Γ} {p : Lit Γ}
                       → Backjump-suffix tr tr'
                       → (cg< : count-guessed tr' < sizeₛ Γ)
                       → Rejstk-Inv rj tr
                       → Rejstk-Inv (bump-at (ℕ→fin (count-guessed tr') cg<) p rj)
                                    ((negate p , deduced) ∷ tr')
bump-rejstkinv-deduced {Γ} {rj} {tr} {tr'} {p} bjsf cg< ri x f x∈ =
  Dec.elim
    {C = λ q → x ∈ₛ (if ⌊ q ⌋
                       then lookupᵥ rj f
                       else if fin→ℕ f == fin→ℕ z
                              then p ∷ lookupᵥ rj f
                              else [])
             → negate x ∈ trail-lits (drop-guessed ((negate p , deduced) ∷ tr')
                                                   (count-guessed tr' ∸ fin→ℕ f))}
    (λ lt x∈ →
         let lt' = <-≤-trans lt (=→≤ (ℕ→fin→ℕ _ cg<)) in
         subst (λ q → negate x ∈ trail-lits q)
                (drop-guessed-++-l {pr = (negate p , deduced) ∷ []} {tr = tr'} {n = count-guessed tr' ∸ fin→ℕ f}
                   (id ∷ [])
                   (∸>0≃> ⁻¹ $ lt') ⁻¹) $
         subst (λ q → negate x ∈ trail-lits (drop-guessed q (count-guessed tr' ∸ fin→ℕ f)))
               (bjsf ⁻¹) $
         subst (λ q → negate x ∈ trail-lits q)
               (drop-guessed-+ {n = count-guessed tr ∸ count-guessed tr'} {m = count-guessed tr' ∸ fin→ℕ f} ⁻¹) $
         subst (λ q → negate x ∈ trail-lits (drop-guessed tr q))
               (  ap (_∸ fin→ℕ f)
                          (∸+=id (count-guessed tr') (count-guessed tr)
                            (bjsuffix-cg bjsf) ⁻¹)
                ∙ +∸-assoc (count-guessed tr ∸ count-guessed tr') (count-guessed tr') (fin→ℕ f)
                           (<-weaken _ _ lt') ⁻¹) $
         ri x f x∈)
    (λ ge →
         Dec.elim
             {C = λ q → x ∈ₛ (if ⌊ q ⌋ then p ∷ lookupᵥ rj f else [])
                      → negate x ∈ trail-lits (drop-guessed ((negate p , deduced) ∷ tr')
                                                            (count-guessed tr' ∸ fin→ℕ f))}
             (λ e x∈ →
                 let e' = e ∙ ℕ→fin→ℕ _ cg< in
                  subst (λ q → negate x ∈ trail-lits (drop-guessed ((negate p , deduced) ∷ tr') q))
                        (  ap (count-guessed tr' ∸_) e' ⁻¹) $
                  subst (λ q → negate x ∈ trail-lits (drop-guessed ((negate p , deduced) ∷ tr') q))
                        (∸-cancel (count-guessed tr') ⁻¹) $
                  [ (λ x=p → here (ap negate x=p))
                  , (λ x∈' → there $
                             subst (λ q → negate x ∈ trail-lits q)
                                   (bjsf ⁻¹) $
                             subst (λ q → negate x ∈ trail-lits (drop-guessed tr (count-guessed tr ∸ q)))
                                   e' $
                             ri x f x∈')
                  ]ᵤ $
                  ∈ₛ-∷→ x∈)
             (λ ne → false! ⦃ Refl-x∉ₛ[] ⦄)
             (ℕ-is-discrete {x = fin→ℕ f} {y = fin→ℕ z}))
    (<-dec {x = fin→ℕ f} {x = fin→ℕ z})
    (subst (x ∈_)
           (lookup-tabulate {f = bump-at-fun p rj (fin→ℕ z)} f)
           x∈)
  where
  z : Fin (sizeₛ Γ)
  z = ℕ→fin (count-guessed tr') cg<

push-rejstkinv-guessed : {rj : Rejstk Γ} {tr tr' : Trail Γ} {p : Lit Γ}
                       → USP-suffix tr' tr
                       → Rejstk-Inv rj tr
                       → Rejstk-Inv rj ((p , guessed) ∷ tr')
push-rejstkinv-guessed {tr} {tr'} {p} us ri x f x∈ =
  let nx∈ = ri x f x∈ in
  Dec.rec
    (λ le →
        subst (λ q → negate x ∈ trail-lits (drop-guessed ((p , guessed) ∷ tr') q))
              (≤→∸=0 le ⁻¹) $
        there $
        subst (λ q → negate x ∈ trail-lits q)
               (us .snd .snd ⁻¹) $
        subst (negate x ∈_)
              (trail-lits-++ {tr1 = us .fst} ⁻¹) $
        any-++-r {xs = trail-lits (us .fst)} $
        subst (λ q → negate x ∈ trail-lits (drop-guessed tr q))
              (≤→∸=0 (=→≤ (uspsuffix→count-guessed us) ∙ ≤-ascend ∙ le)) $
        nx∈)
    (λ ge →
        let le' = ≤≃<suc ⁻¹ $ ≱→< ge in
        subst (λ q → negate x ∈ trail-lits (drop-guessed ((p , guessed) ∷ tr') q))
              (+∸-assoc _ _ _ le') $
        subst (λ q → negate x ∈ trail-lits (drop-guessed tr' (q ∸ fin→ℕ f)))
              (uspsuffix→count-guessed us) $
        subst (λ q → negate x ∈ trail-lits (drop-guessed q (count-guessed tr ∸ fin→ℕ f)))
              (us .snd .snd ⁻¹) $
        [ (λ lt' →
              subst (λ q → negate x ∈ trail-lits q)
                    (drop-guessed-++-l
                       {pr = us .fst} {n = count-guessed tr ∸ fin→ℕ f}
                       (us .snd .fst)
                       (∸>0≃> ⁻¹ $ <-≤-trans lt' (=→≤ (uspsuffix→count-guessed us ⁻¹)))
                       ⁻¹) $
              nx∈)
        , (λ e' →
             let e'' = ≤→∸=0 (=→≤ (uspsuffix→count-guessed us ∙ e' ⁻¹)) in
             subst (λ q → negate x ∈ trail-lits (drop-guessed (us .fst ++ tr) q))
                   (e'' ⁻¹) $
             subst (negate x ∈_)
                   (trail-lits-++ {tr1 = us .fst} ⁻¹) $
             any-++-r {xs = trail-lits (us .fst)} $
             subst (λ q → negate x ∈ trail-lits (drop-guessed tr q))
                   e'' $
             nx∈)
        ]ᵤ (≤→<⊎= le'))
    (≤-dec {x = suc (count-guessed tr')} {x = fin→ℕ f})

-- the algorithm

USP-ty : ℕ → 𝒰
USP-ty x = {Γ : Ctx}
         → CNF Γ → (tr : Trail Γ)
         → x ＝ 2 · sizeₛ Γ ∸ length tr
         → Trail-Inv tr
         → Trail-Inv2 tr
         → CNF Γ × (Σ[ tr' ꞉ Trail Γ ] (  Trail-Inv tr'
                                        × Trail-Inv2 tr'
                                        × USP-suffix tr' tr))

unit-subpropagate-loop : ∀[ □ USP-ty ⇒ USP-ty ]
unit-subpropagate-loop {x} ih {Γ} cls tr e ti ti2 =
  Dec.rec (λ _ →   cls' , tr
                 , ti , ti2 , [] , [] , refl)
          (λ ne → let (  cls0 , tr0
                       , ti0 , ti20 , (pr0 , a0 , e0)) =
                         Box.call ih (prf ne)
                           cls' tr'
                           refl ti' ti2'
                  in ( cls0 , tr0
                     , ti0 , ti20
                     , (  pr0 ++ tru
                        , all-++ a0 (all→map (all-trivial (λ _ → id)))
                        , e0 ∙ ++-assoc pr0 _ tr ⁻¹)))
          (Dec-is-nil? {xs = newunits})
  where
  cls' = map (filter (not ∘ trail-has tr ∘ negate)) cls
  newunits = unions (filter (is-fresh-unit-clause tr) cls')
  tru = map (_, deduced) newunits
  tr' = tru ++ tr

  -- propositional (proof) part
  -- TODO streamline
  nueq : trail-lits tru ＝ newunits
  nueq = happly map-pres-comp newunits ⁻¹ ∙ happly map-pres-id newunits

  tiu : Trail-Inv tru
  tiu =
    uniq-map unpack-inj $
    subst Uniq (nueq ⁻¹) $
    nub-unique {R = λ _ _ → Lit-is-discrete .proof}
               {xs = concat (filter (is-fresh-unit-clause tr) cls')}

  dju : trail-lits tru ∥ trail-lits tr
  dju =
    subst (_∥ trail-lits tr) (nueq ⁻¹) $
    λ {x} x∈nu x∈tr →
     let (zs , zs∈ , x∈') = ∈-concat {xss = filter (is-fresh-unit-clause tr) cls'}
                            (ope→subset {ys = concat (filter (is-fresh-unit-clause tr) cls')}
                              (nub-ope {cmp = _=?_}) x∈nu)
         (fzs , _) = filter-∈ {p = is-fresh-unit-clause tr} {xs = cls'} zs∈
         (lz , zse , ll) = fresh-unit-clause-prop {c = zs} fzs
        in
      ll $
      subst (_∈ trail-lits tr)
            (any-¬there false! (subst (x ∈_) zse x∈'))
            x∈tr

  ti' : Trail-Inv tr'
  ti' = prepend-trailinv tiu ti dju

  ti2' : Trail-Inv2 tr'
  ti2' = prepend-deduced-trailinv2 (all→map $ all-trivial λ _ → id) tiu ti dju ti2

  prf : newunits ≠ [] → 2 · sizeₛ Γ ∸ length tr' < x
  prf ne =
    <-≤-trans
      (<-∸-2l-≃ (trail-inv≤ ti') ⁻¹ $
       <-≤-trans
         (<-+-0lr (<-≤-trans
                     (≱→< $ contra (length=0→nil ∘ ≤0→=0) ne)
                     (=→≤ (map-length ⁻¹))))
         (=→≤ (++-length _ tr ⁻¹)))
      (=→≤ (e ⁻¹))

unit-propagate-iter : {Γ : Ctx}
                    → CNF Γ → (tr : Trail Γ) → Trail-Inv tr → Trail-Inv2 tr
                    → CNF Γ × (Σ[ tr' ꞉ Trail Γ ] (  Trail-Inv tr'
                                                   × Trail-Inv2 tr'
                                                   × USP-suffix tr' tr))
unit-propagate-iter cls tr ti ti2 =
  Box.fix USP-ty unit-subpropagate-loop cls tr refl ti ti2

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
  Maybe.elim (λ m → backtrack tr ＝ m → Σ[ tr' ꞉ Trail Γ ] (Trail-Inv tr' × Trail-Inv2 tr' × Backjump-suffix tr tr'))
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
    (λ cp → Maybe.elim (λ m → backtrack tr ＝ m → Bool)
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
     -- put-str-ln $ "prime(DPLI) 13: " ++ₛ ppFBᵢ dplitaut (prime 13)
     -- put-str-ln $ "prime(DPLI) 16: " ++ₛ ppFBᵢ dplitaut (prime 16)
     put-str-ln $ "prime(DPLI) 21: " ++ₛ ppFBᵢ dplitaut (prime 21)
-}
