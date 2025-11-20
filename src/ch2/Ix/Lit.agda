{-# OPTIONS --no-exact-split #-}
module ch2.Ix.Lit where

open import Prelude hiding (_≠_)
open import Meta.Effect hiding (_>>_ ; _>>=_)
open import Meta.Show
open import Logic.Discreteness
open import System.Everything hiding (_<$>_)

open import Data.Unit
open import Data.Empty
open import Data.Bool as Bool
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
open import Data.List.Operations.Discrete
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Operations.Rel
open import Data.Sum

open import Data.List.NonEmpty as List⁺

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import ListSet
open import ch2.Formula
open import ch2.Sem
open import ch2.Ix.Formula

private variable
  A B C : 𝒰
  Γ : LFSet A

-- literals

data Lit (Γ : LFSet A) : 𝒰 where
  Pos : (a : A) → a ∈ Γ → Lit Γ
  Neg : (a : A) → a ∈ Γ → Lit Γ

unlit : {Γ : LFSet A}
      → Lit Γ → A
unlit (Pos a _) = a
unlit (Neg a _) = a

is-pos : Lit Γ → Type
is-pos (Pos x _) = ⊤
is-pos (Neg x _) = ⊥

pos≠neg : {Γ : LFSet A} {x y : A} {mx : x ∈ Γ} {my : y ∈ Γ}
        → Pos x mx ≠ Neg y my
pos≠neg p = subst is-pos p tt

Lit-= : {Γ : LFSet A}
      → (A → A → Bool)
      → Lit Γ → Lit Γ → Bool
Lit-= e (Pos x _) (Pos y _) = e x y
Lit-= e (Pos x _) (Neg y _) = false
Lit-= e (Neg x _) (Pos y _) = false
Lit-= e (Neg x _) (Neg y _) = e x y

Reflects-lit : {Γ : LFSet A} {e : A → A → Bool}
             → (∀ {x y} → Reflects (x ＝ y) (e x y))
             → ∀ {lx ly : Lit Γ} → Reflects (lx ＝ ly) (Lit-= e lx ly)
Reflects-lit re {lx = Pos x mx} {ly = Pos y my} = Reflects.dmap (λ x → ap² Pos x (to-pathᴾ (hlevel 1 _ my))) (contra (ap unlit)) re
Reflects-lit re {lx = Pos x mx} {ly = Neg y my} = ofⁿ pos≠neg
Reflects-lit re {lx = Neg x mx} {ly = Pos y my} = ofⁿ (pos≠neg ∘ _⁻¹)
Reflects-lit re {lx = Neg x mx} {ly = Neg y my} = Reflects.dmap (λ x → ap² Neg x (to-pathᴾ (hlevel 1 _ my))) (contra (ap unlit)) re

instance
  Lit-is-discrete : {Γ : LFSet A} → ⦃ d : is-discrete A ⦄ → is-discrete (Lit Γ)
  Lit-is-discrete ⦃ d ⦄ {x} {y} .does  = Lit-= (λ x y → d {x = x} {y = y} .does) x y
  Lit-is-discrete ⦃ d ⦄         .proof = Reflects-lit (d .proof)

  Show-lit : {Γ : LFSet A} → ⦃ s : Show A ⦄ → Show (Lit Γ)
  Show-lit = default-show λ where
                              (Pos x _) → show x
                              (Neg x _) → "¬" ++ₛ show x

negative : Lit Γ → Bool
negative (Neg _ _) = true
negative  _        = false

positive : Lit Γ → Bool
positive = not ∘ negative

abs : Lit Γ → Lit Γ
abs (Neg p mp) = Pos p mp
abs (Pos p mp) = Pos p mp

abs-idem : {l : Lit Γ}
         → abs (abs l) ＝ abs l
abs-idem {l = Pos a m} = refl
abs-idem {l = Neg a m} = refl

negate : Lit Γ → Lit Γ
negate (Neg p mp) = Pos p mp
negate (Pos p mp) = Neg p mp

abs-negate : {l : Lit Γ}
           → abs (negate l) ＝ abs l
abs-negate {l = Pos a m} = refl
abs-negate {l = Neg a m} = refl

restrict : {Γ : LFSet A}
         → (l : Lit Γ) → Lit (sng (unlit l))
restrict (Pos a _) = Pos a (hereₛ refl)
restrict (Neg a _) = Neg a (hereₛ refl)

wk-lit : {Γ Δ : LFSet A} → Γ ⊆ Δ → Lit Γ → Lit Δ
wk-lit f (Pos a m) = Pos a (f m)
wk-lit f (Neg a m) = Neg a (f m)

wk-lit-inj : {Γ Δ : LFSet A} {s : Γ ⊆ Δ}
           → Injective (wk-lit s)
wk-lit-inj {s = s} {x = Pos a x} {y = Pos b y} e =
  ap² Pos (ap unlit e) (to-pathᴾ (hlevel 1 _ y))
wk-lit-inj {s = s} {x = Pos a x} {y = Neg b y} e =
  absurd (pos≠neg e)
wk-lit-inj {s = s} {x = Neg a x} {y = Pos b y} e =
  absurd (pos≠neg (e ⁻¹))
wk-lit-inj {s = s} {x = Neg a x} {y = Neg b y} e =
  ap² Neg (ap unlit e) (to-pathᴾ (hlevel 1 _ y))

negate-invol : {l : Lit Γ}
             → negate (negate l) ＝ l
negate-invol {l = Pos a m} = refl
negate-invol {l = Neg a m} = refl

negate-swap : {l m : Lit Γ}
            → l ＝ negate m
            → m ＝ negate l
negate-swap e = negate-invol ⁻¹ ∙ ap negate (e ⁻¹)

negative-negate : {l : Lit Γ}
                → negative (negate l) ＝ positive l
negative-negate {l = Pos a x} = refl
negative-negate {l = Neg a x} = refl

-- TODO should probably generalized to involutive→injective (or embedding?)
negate-inj : {Γ : LFSet A}
           → Injective (negate {Γ = Γ})
negate-inj {x} {y} e = negate-invol {l = x} ⁻¹ ∙ ap negate e ∙ negate-invol {l = y}

unlit-eq : {Γ : LFSet A} {x y : Lit Γ}
         → unlit x ＝ unlit y
         → (x ＝ y) ⊎ (x ＝ negate y)
unlit-eq {x = Pos a x} {y = Pos b y} e =
  inl (ap² Pos e (to-pathᴾ (hlevel 1 _ y)))
unlit-eq {x = Pos a x} {y = Neg b y} e =
  inr (ap² Pos e (to-pathᴾ (hlevel 1 _ y)))
unlit-eq {x = Neg a x} {y = Pos b y} e =
  inr (ap² Neg e (to-pathᴾ (hlevel 1 _ y)))
unlit-eq {x = Neg a x} {y = Neg b y} e =
  inl (ap² Neg e (to-pathᴾ (hlevel 1 _ y)))

unlit-negate : {Γ : LFSet A} {x : Lit Γ}
             → unlit x ＝ unlit (negate x)
unlit-negate {x = Pos a x} = refl
unlit-negate {x = Neg a x} = refl

unpack : {Γ : LFSet A} → Lit Γ → A × Bool
unpack = < unlit , positive >

unpack-inj : {Γ : LFSet A}
           → Injective (unpack {Γ = Γ})
unpack-inj {x = Pos a x} {y = Pos b y} e =
  ap² Pos (ap fst e) (to-pathᴾ (hlevel 1 _ y))
unpack-inj {x = Pos a x} {y = Neg b y} e =
  false! (ap snd e)
unpack-inj {x = Neg a x} {y = Pos b y} e =
  false! (ap snd e)
unpack-inj {x = Neg a x} {y = Neg b y} e =
  ap² Neg (ap fst e) (to-pathᴾ (hlevel 1 _ y))

unlit∈ : (l : Lit Γ) → unlit l ∈ Γ
unlit∈ (Pos a m) = m
unlit∈ (Neg a m) = m

lit→form : {Γ : LFSet A}
         → Lit Γ → Formulaᵢ Γ
lit→form (Pos a m) = Atom a m
lit→form (Neg a m) = Not (Atom a m)

-- applies to both Clauses and Conjuncts
nontrivial? : {Γ : LFSet A}
            → ⦃ d : is-discrete A ⦄
            → List (Lit Γ) → Bool
nontrivial? c =
  let (p , n) = partition positive c in
  is-nil? $ intersect p $ image negate n

-- nontrivial = no literal is included both positively and negatively
Reflects-nontrivial? : {Γ : LFSet A}
                     → ⦃ di : is-discrete A ⦄
                     → {c : List (Lit Γ)}
                     → Reflects ({l : Lit Γ} → l ∈ c → negate l ∈ c → ⊥)
                                (nontrivial? c)
Reflects-nontrivial? ⦃ di ⦄ {c} =
  let (p , n) = partition positive c
      e = partition-filter {p = positive} {xs = c}
      (ep , en) = ×-path-inv e
      op = subst (λ q → OPE q c) (ep ⁻¹) filter-OPE
      on = subst (λ q → OPE q c) (en ⁻¹) filter-OPE
    in
  Reflects.dmap
    (λ d {l} l∈ n∈ →
       Dec.rec
         (λ lp → d (subst (l ∈_) (ep ⁻¹) $
                    ∈-filter lp l∈)
                   (subst (λ q → l ∈ image negate q) (en ⁻¹) $
                    ⊆-nub {R = λ _ _ → Reflects-lit (di .proof)} $
                    subst (λ q → q ∈ map negate (filter (not ∘ positive) c)) negate-invol $
                    List.∈-map negate $
                    ∈-filter (subst So (negative-negate ⁻¹ ∙ not-invol _ ⁻¹) lp) n∈))
         (λ ln → let ln′ = not-so-≃ ⁻¹ $ ln in
                 d (subst (negate l ∈_) (ep ⁻¹) $
                    ∈-filter (subst (So ∘ not) (negative-negate ⁻¹) ln′) n∈)
                   (⊆-nub {R = λ _ _ → Reflects-lit (di .proof)} $
                    List.∈-map negate $
                    subst (l ∈_) (en ⁻¹) $
                    ∈-filter ln′ l∈))
         (Dec-So {b = positive l}))
    (contra λ d l∈p l∈n →
              d (ope→subset op l∈p)
                (ope→subset on $
                 map-∈ negate negate-inj $
                 subst (_∈ map negate n) (negate-invol ⁻¹) $
                 ope→subset nub-ope l∈n))
    Reflects-intersect-disjoint

Dec-nontrivial? : {Γ : LFSet A}
                → ⦃ di : is-discrete A ⦄
                → (c : List (Lit Γ))
                → Dec ({l : Lit Γ} → l ∈ c → negate l ∈ c → ⊥)
Dec-nontrivial? c .does  = nontrivial? c
Dec-nontrivial? c .proof = Reflects-nontrivial?

{-
trivial? : {Γ : LFSet A}
         → ⦃ d : is-discrete A ⦄
         → List (Lit Γ) → Bool
trivial? c =
  let (p , n) = partition positive c in
  is-cons? $ intersect p $ image negate n
-}

map-unlit-⊆ : {Γ : LFSet A}
            → ⦃ d : is-discrete A ⦄
            → (ls : List (Lit Γ)) → mapₛ unlit (LFSet.from-list ls) ⊆ Γ
map-unlit-⊆ {Γ} ls =
    rec! (λ l _ e → subst (_∈ Γ) (e ⁻¹) (unlit∈ l))
  ∘ mapₛ-∈ {s = LFSet.from-list ls}

polarize : LFSet A → LFSet (A × Bool)
polarize Γ = mapₛ (_, true) Γ ∪∷ mapₛ (_, false) Γ

size-polarize : {Γ : LFSet A}
              → ⦃ di : is-discrete A ⦄
              → sizeₛ (polarize Γ) ＝ sizeₛ Γ + sizeₛ Γ
size-polarize =
    size-∪∷-∥ₛ
      (λ x∈t x∈f →
          rec! (λ xt xt∈ xte →
                 rec! (λ xf xf∈ xfe →
                        false! (ap snd xte ⁻¹ ∙ ap snd xfe))
                      (mapₛ-∈ x∈f))
               (mapₛ-∈ x∈t))
  ∙ ap² _+_ (size-map-inj (ap fst))
            (size-map-inj (ap fst))

lit-set⊆ : {Γ : LFSet A}
         → ⦃ di : is-discrete A ⦄
         → {l : LFSet (Lit Γ)}
         → mapₛ unpack l ⊆ polarize Γ
lit-set⊆ {Γ} {x = xl , xb} x∈ =
  rec!
    (λ y y∈ ye →
        Bool.elim
           {P = λ q → (xl , q) ∈ₛ mapₛ (_, q) Γ → (xl , q) ∈ₛ polarize Γ}
            ∈ₛ-∪∷←l
           (∈ₛ-∪∷←r {s₁ = mapₛ (_, true) Γ})
           xb (∈-mapₛ {f = _, xb} (subst (_∈ Γ) (ap fst ye ⁻¹) (unlit∈ y))))
    (mapₛ-∈ x∈)

lit-set-size : {Γ : LFSet A}
             → ⦃ di : is-discrete A ⦄
             → {l : LFSet (Lit Γ)}
             → sizeₛ l ≤ 2 · sizeₛ Γ
lit-set-size {Γ} =
    =→≤ (size-map-inj unpack-inj ⁻¹)
  ∙ size-⊆ lit-set⊆
  ∙ =→≤ (size-polarize ∙ ap (sizeₛ Γ +_) (+-zero-r (sizeₛ Γ) ⁻¹))

lit-< : {Γ : LFSet A}
      → (A → A → Bool)
      → Lit Γ → Lit Γ → Bool
lit-< ord (Pos v1 _) (Pos v2 _) = ord v1 v2
lit-< _   (Pos _ _ ) (Neg _ _)  = true
lit-< _   (Neg _ _)  (Pos _ _)  = false
lit-< ord (Neg v1 _) (Neg v2 _) = ord v1 v2

-- extended literals

data ELit (Γ : LFSet A) : 𝒰 where
  elit   : Lit Γ → ELit Γ
  etrue  : ELit Γ
  efalse : ELit Γ

unelit : ELit Γ → Maybe (Lit Γ)
unelit (elit l) = just l
unelit  _       = nothing

is-elit : ELit Γ → 𝒰
is-elit (elit _) = ⊤
is-elit  _       = ⊥

is-etrue : ELit Γ → 𝒰
is-etrue etrue = ⊤
is-etrue _     = ⊥

elit≠etrue : {l : Lit Γ} → elit l ≠ etrue
elit≠etrue p = subst is-elit p tt

elit≠efalse : {l : Lit Γ} → elit l ≠ efalse
elit≠efalse p = subst is-elit p tt

etrue≠efalse : etrue {Γ = Γ} ≠ efalse
etrue≠efalse p = subst is-etrue p tt

elit-= : {Γ : LFSet A}
       → (A → A → Bool)
       → ELit Γ → ELit Γ → Bool
elit-= e (elit l1) (elit l2) = Lit-= e l1 l2
elit-= e (elit _)  etrue     = false
elit-= e (elit _)  efalse    = false
elit-= e  etrue   (elit _)   = false
elit-= e  etrue    etrue     = true
elit-= e  etrue    efalse    = false
elit-= e  efalse  (elit _)   = false
elit-= e  efalse   etrue     = false
elit-= e  efalse   efalse    = true

Reflects-elit : {Γ : LFSet A} {e : A → A → Bool}
              → (∀ {x y} → Reflects (x ＝ y) (e x y))
              → ∀ {lx ly} → Reflects (lx ＝ ly) (elit-= {Γ = Γ} e lx ly)
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
  ELit-is-discrete : {Γ : LFSet A} → ⦃ d : is-discrete A ⦄ → is-discrete (ELit Γ)
  ELit-is-discrete ⦃ d ⦄ {x} {y} .does  = elit-= (λ x y → d {x = x} {y = y} .does) x y
  ELit-is-discrete ⦃ d ⦄         .proof = Reflects-elit (d .proof)

  Show-elit : {Γ : LFSet A} → ⦃ s : Show A ⦄ → Show (ELit Γ)
  Show-elit = default-show λ where
                              (elit l) → show l
                              etrue → "T"
                              efalse → "F"

elit→form : ELit Γ → Formulaᵢ Γ
elit→form (elit l) = lit→form l
elit→form  etrue   = True
elit→form  efalse  = False

negelit : ELit Γ → ELit Γ
negelit (elit x) = elit (negate x)
negelit etrue = efalse
negelit efalse = etrue

enegative : ELit Γ → Bool
enegative (elit l) = negative l
enegative  efalse  = true
enegative  _       = false

epositive : ELit Γ → Bool
epositive = not ∘ enegative

enegate : ELit Γ → ELit Γ
enegate (elit l) = elit (negate l)
enegate  etrue   = efalse
enegate  efalse  = etrue

eabs : ELit Γ → ELit Γ
eabs lit = if enegative lit then enegate lit else lit

eunpack : {Γ : LFSet A} → ELit Γ → Maybe A × Bool
eunpack = < map unlit ∘ unelit , epositive >

epolarize : LFSet A → LFSet (Maybe A × Bool)
epolarize Γ = (nothing , true) ∷ (nothing , false) ∷ mapₛ (first just) (polarize Γ)

unelit-negative : {y : Lit Γ} {x : ELit Γ}
                → y ∈ unelit x
                → negative y ＝ enegative x
unelit-negative {x = elit x} = ap negative ∘ unhere

-- TODO generalize, move to cm somewhere
first-inj : {f : A → B} {C : 𝒰}
          → Injective f
          → Injective (first {A = A} {C = λ _ → C} f)
first-inj finj e = ×-path (finj $ ap fst e) (ap snd e)

eunpack-inj : {Γ : LFSet A}
            → Injective (eunpack {Γ = Γ})
eunpack-inj {x = elit x} {y = elit y} e =
  ap elit $
  unpack-inj $
  first-inj just-inj e
eunpack-inj {x = elit x} {y = etrue}  e = false! (ap fst e)
eunpack-inj {x = elit x} {y = efalse} e = false! (ap fst e)
eunpack-inj {x = etrue}  {y = elit y} e = false! (ap fst e)
eunpack-inj {x = etrue}  {y = etrue}  e = refl
eunpack-inj {x = etrue}  {y = efalse} e = false! (ap snd e)
eunpack-inj {x = efalse} {y = elit x} e = false! (ap fst e)
eunpack-inj {x = efalse} {y = etrue}  e = false! (ap snd e)
eunpack-inj {x = efalse} {y = efalse} e = refl

size-epolarize : {Γ : LFSet A}
              → ⦃ di : is-discrete A ⦄
              → sizeₛ (epolarize Γ) ＝ 2 + 2 · sizeₛ Γ
size-epolarize {Γ} =
    size-∷
  ∙ ap suc
       (  ap sizeₛ (rem-∉-eq (∉ₛ-∷ (false! ∘ ap snd)
                                   (∉-mapₛ λ x _ → false! ∘ ap fst)))
        ∙ size-∷
        ∙ ap suc (  ap sizeₛ (rem-∉-eq (∉-mapₛ λ x _ → false! ∘ ap fst))
                  ∙ size-map-inj (first-inj just-inj)
                  ∙ size-polarize
                  ∙ ap (sizeₛ Γ +_) (+-zero-r (sizeₛ Γ) ⁻¹)))

elit-set⊆ : {Γ : LFSet A}
          → ⦃ di : is-discrete A ⦄
          → {l : LFSet (ELit Γ)}
          → mapₛ eunpack l ⊆ epolarize Γ
elit-set⊆ {Γ} {l} {x = xm , xb} x∈ =
  rec!
    (λ y y∈ →
        Maybe.elim
           (λ q → (q , xb) ＝ eunpack y → (q , xb) ∈ₛ epolarize Γ)
           (λ _ → Bool.elim
                    {P = λ q → (nothing , q) ∈ₛ epolarize Γ}
                    (hereₛ refl)
                    (thereₛ $ hereₛ refl)
                    xb)
           (λ x xe →
              let (z , z∈ , ze) = Maybe.map-∈Σ unlit (=just→∈ (ap fst xe ⁻¹)) in
              thereₛ $ thereₛ $
              ∈-mapₛ $
              lit-set⊆ $
              subst (_∈ mapₛ unpack (bindₛ (from-maybe ∘ unelit) l))
                    (×-path (ze ⁻¹)
                            (ap not (unelit-negative z∈) ∙ ap snd xe ⁻¹)) $
              ∈-mapₛ $
              ∈-bind y∈ $
              ∈-maybe z∈)
           xm)
    (mapₛ-∈ x∈)

elit-set-size : {Γ : LFSet A}
              → ⦃ di : is-discrete A ⦄
              → {l : LFSet (ELit Γ)}
              → sizeₛ l ≤ 2 + 2 · sizeₛ Γ
elit-set-size {l} =
    =→≤ (size-map-inj eunpack-inj ⁻¹)
  ∙ size-⊆ (elit-set⊆ {l = l})
  ∙ =→≤ (size-epolarize)

elit-< : {Γ : LFSet A}
       → (A → A → Bool)
       → ELit Γ → ELit Γ → Bool
elit-< ord (elit l1) (elit l2) = lit-< ord l1 l2
elit-< _ (elit _)   etrue    = false
elit-< _ (elit _)   efalse   = false
elit-< _  etrue    (elit _)  = true
elit-< _  etrue     etrue    = false
elit-< _  etrue     efalse   = true
elit-< _  efalse   (elit _)  = true
elit-< _  efalse    etrue    = false
elit-< _  efalse    efalse   = false
