{-# OPTIONS --no-exact-split #-}
module ch2.Ix.Lit where

open import Prelude hiding (_≠_)
open import Foundations.Sigma
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
open import ch2.Sem
open import ch2.Ix.Formula

private variable
  A B C : 𝒰
  Γ : LFSet A

-- literals

data Lit (Γ : LFSet A) : 𝒰 where
  Pos : AVar Γ → Lit Γ
  Neg : AVar Γ → Lit Γ

unlit : {Γ : LFSet A}
      → Lit Γ → A
unlit (Pos a) = unvar a
unlit (Neg a) = unvar a

lit→atomvar : Lit Γ → AVar Γ
lit→atomvar (Pos a) = a
lit→atomvar (Neg a) = a

is-pos : Lit Γ → Type
is-pos (Pos _) = ⊤
is-pos (Neg _) = ⊥

pos≠neg : {Γ : LFSet A} {x y : AVar Γ}
        → Pos x ≠ Neg y
pos≠neg p = subst is-pos p tt

Lit-= : {Γ : LFSet A}
      → (A → A → Bool)
      → Lit Γ → Lit Γ → Bool
Lit-= e (Pos x) (Pos y) = e (unvar x) (unvar y)
Lit-= e (Pos x) (Neg y) = false
Lit-= e (Neg x) (Pos y) = false
Lit-= e (Neg x) (Neg y) = e (unvar x) (unvar y)

Reflects-lit : {Γ : LFSet A} {e : A → A → Bool}
             → (∀ {x y} → Reflects (x ＝ y) (e x y))
             → ∀ {lx ly : Lit Γ} → Reflects (lx ＝ ly) (Lit-= e lx ly)
Reflects-lit re {lx = Pos x} {ly = Pos y} = Reflects.dmap (ap Pos ∘ avar-ext) (contra (ap unlit)) re
Reflects-lit re {lx = Pos x} {ly = Neg y} = ofⁿ pos≠neg
Reflects-lit re {lx = Neg x} {ly = Pos y} = ofⁿ (pos≠neg ∘ _⁻¹)
Reflects-lit re {lx = Neg x} {ly = Neg y} = Reflects.dmap (ap Neg ∘ avar-ext) (contra (ap unlit)) re

instance
  Lit-is-discrete : {Γ : LFSet A} → ⦃ d : is-discrete A ⦄ → is-discrete (Lit Γ)
  Lit-is-discrete ⦃ d ⦄ {x} {y} .does  = Lit-= (λ x y → d {x = x} {y = y} .does) x y
  Lit-is-discrete ⦃ d ⦄         .proof = Reflects-lit (d .proof)

  Show-lit : {Γ : LFSet A} → ⦃ s : Show A ⦄ → Show (Lit Γ)
  Show-lit = default-show λ where
                              (Pos x) → show ⦃ r = Show-avar ⦄ x
                              (Neg x) → "¬" ++ₛ show ⦃ r = Show-avar ⦄ x

negative : Lit Γ → Bool
negative (Neg _) = true
negative  _      = false

positive : Lit Γ → Bool
positive = not ∘ negative

abs : Lit Γ → Lit Γ
abs (Neg p) = Pos p
abs (Pos p) = Pos p

abs-idem : {l : Lit Γ}
         → abs (abs l) ＝ abs l
abs-idem {l = Pos a} = refl
abs-idem {l = Neg a} = refl

negate : Lit Γ → Lit Γ
negate (Neg p) = Pos p
negate (Pos p) = Neg p

abs-negate : {l : Lit Γ}
           → abs (negate l) ＝ abs l
abs-negate {l = Pos a} = refl
abs-negate {l = Neg a} = refl

restrict : {Γ : LFSet A}
         → (l : Lit Γ) → Lit (sng (unlit l))
restrict (Pos a) = Pos (restrict-avar a)
restrict (Neg a) = Neg (restrict-avar a)

wk-lit : {Γ Δ : LFSet A} → Γ ⊆ Δ → Lit Γ → Lit Δ
wk-lit s (Pos a) = Pos (wk-avar s a)
wk-lit s (Neg a) = Neg (wk-avar s a)

wk-lit-inj : {Γ Δ : LFSet A} {s : Γ ⊆ Δ}
           → Injective (wk-lit s)
wk-lit-inj {x = Pos a} {y = Pos b} e =
  ap Pos (avar-ext (ap unlit e))
wk-lit-inj {x = Pos a} {y = Neg b} e =
  absurd (pos≠neg e)
wk-lit-inj {x = Neg a} {y = Pos b} e =
  absurd (pos≠neg (e ⁻¹))
wk-lit-inj {x = Neg a} {y = Neg b} e =
  ap Neg (avar-ext (ap unlit e))

-- no-ops propagating context strengthenings
avoid-lit-var : ⦃ d : is-discrete A ⦄ → {v : A} → (l : Lit Γ) → v ≠ unlit l → Lit (rem v Γ)
avoid-lit-var (Pos a) ne = Pos (avoid-var a ne)
avoid-lit-var (Neg a) ne = Neg (avoid-var a ne)

avoid-lit-ctx : ⦃ d : is-discrete A ⦄ → (l : Lit Γ) → {Δ : LFSet A} → unlit l ∉ Δ → Lit (minus Γ Δ)
avoid-lit-ctx (Pos a) l∉ = Pos (avoid-ctx a l∉)
avoid-lit-ctx (Neg a) l∉ = Neg (avoid-ctx a l∉)

negate-invol : {l : Lit Γ}
             → negate (negate l) ＝ l
negate-invol {l = Pos a} = refl
negate-invol {l = Neg a} = refl

negate-swap : {l m : Lit Γ}
            → l ＝ negate m
            → m ＝ negate l
negate-swap e = negate-invol ⁻¹ ∙ ap negate (e ⁻¹)

negative-negate : {l : Lit Γ}
                → negative (negate l) ＝ positive l
negative-negate {l = Pos a} = refl
negative-negate {l = Neg a} = refl

-- TODO should probably generalized to involutive→injective (or embedding?)
negate-inj : {Γ : LFSet A}
           → Injective (negate {Γ = Γ})
negate-inj {x} {y} e = negate-invol {l = x} ⁻¹ ∙ ap negate e ∙ negate-invol {l = y}

unlit-eq : {Γ : LFSet A} {x y : Lit Γ}
         → unlit x ＝ unlit y
         → (x ＝ y) ⊎ (x ＝ negate y)
unlit-eq {x = Pos a} {y = Pos b} e =
  inl (ap Pos (avar-ext e))
unlit-eq {x = Pos a} {y = Neg b} e =
  inr (ap Pos (avar-ext e))
unlit-eq {x = Neg a} {y = Pos b} e =
  inr (ap Neg (avar-ext e))
unlit-eq {x = Neg a} {y = Neg b} e =
  inl (ap Neg (avar-ext e))

unlit-negate : {Γ : LFSet A} {x : Lit Γ}
             → unlit x ＝ unlit (negate x)
unlit-negate {x = Pos a} = refl
unlit-negate {x = Neg a} = refl

unpack : {Γ : LFSet A} → Lit Γ → A × Bool
unpack = < unlit , positive >

unpack-inj : {Γ : LFSet A}
           → Injective (unpack {Γ = Γ})
unpack-inj {x = Pos a} {y = Pos b} e =
  ap Pos (avar-ext (ap fst e))
unpack-inj {x = Pos a} {y = Neg b} e =
  false! (ap snd e)
unpack-inj {x = Neg a} {y = Pos b} e =
  false! (ap snd e)
unpack-inj {x = Neg a} {y = Neg b} e =
  ap Neg (avar-ext (ap fst e))

unlit∈ : (l : Lit Γ) → unlit l ∈ Γ
unlit∈ (Pos a) = unvar∈ a
unlit∈ (Neg a) = unvar∈ a

lit→form : {Γ : LFSet A}
         → Lit Γ → Formulaᵢ Γ
lit→form (Pos a) = Atom a
lit→form (Neg a) = Not (Atom a)

wk-lit-form : {Γ Δ : LFSet A} {s : Γ ⊆ Δ}
            → (l : Lit Γ)
            → lit→form (wk-lit s l) ＝ wk s (lit→form l)
wk-lit-form {s} (Pos a) = refl
wk-lit-form {s} (Neg a) = refl

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
lit-< ord (Pos v1) (Pos v2) = ord (unvar v1) (unvar v2)
lit-< _   (Pos _ ) (Neg _)  = true
lit-< _   (Neg _ ) (Pos _)  = false
lit-< ord (Neg v1) (Neg v2) = ord (unvar v1) (unvar v2)

-- extended literals

data ELit (Γ : LFSet A) : 𝒰 where
  elit   : Lit Γ → ELit Γ
  etrue  : ELit Γ
  efalse : ELit Γ

unelit : ELit Γ → Maybe (Lit Γ)
unelit (elit l) = just l
unelit  _       = nothing

unevar : {Γ : LFSet A} → ELit Γ → Maybe A
unevar = map unlit ∘ unelit

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

elit-inj : {l1 l2 : Lit Γ}
         → elit l1 ＝ elit l2
         → l1 ＝ l2
elit-inj = just-inj ∘ ap unelit

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

enegative? : ELit Γ → Bool
enegative? (elit l) = negative l
enegative?  efalse  = true
enegative?  _       = false

epositive? : ELit Γ → Bool
epositive? = not ∘ enegative?

enegate : ELit Γ → ELit Γ
enegate (elit l) = elit (negate l)
enegate  etrue   = efalse
enegate  efalse  = etrue

enegative-enegate : {l : ELit Γ}
                  → enegative? (enegate l) ＝ epositive? l
enegative-enegate {l = elit l} = negative-negate {l = l}
enegative-enegate {l = etrue}  = refl
enegative-enegate {l = efalse} = refl

eabs : ELit Γ → ELit Γ
eabs lit = if enegative? lit then enegate lit else lit

eunpack : {Γ : LFSet A} → ELit Γ → Maybe A × Bool
eunpack = < unevar , epositive? >

epolarize : LFSet A → LFSet (Maybe A × Bool)
epolarize Γ = (nothing , true) ∷ (nothing , false) ∷ mapₛ (first just) (polarize Γ)

unelit-negative : {y : Lit Γ} {x : ELit Γ}
                → y ∈ unelit x
                → negative y ＝ enegative? x
unelit-negative {x = elit x} = ap negative ∘ unhere

wk-elit : {Γ Δ : LFSet A} → Γ ⊆ Δ → ELit Γ → ELit Δ
wk-elit s (elit l) = elit $ wk-lit s l
wk-elit s  etrue   = etrue
wk-elit s  efalse  = efalse

wk-elit-inj : {Γ Δ : LFSet A} {s : Γ ⊆ Δ}
            → Injective (wk-elit s)
wk-elit-inj {x = elit x} {y = elit y} e =
  ap elit (wk-lit-inj (elit-inj e))
wk-elit-inj {x = elit x} {y = etrue}  e = absurd (elit≠etrue e)
wk-elit-inj {x = elit x} {y = efalse} e = absurd (elit≠efalse e)
wk-elit-inj {x = etrue}  {y = elit x} e = absurd (elit≠etrue (e ⁻¹))
wk-elit-inj {x = etrue}  {y = etrue}  e = refl
wk-elit-inj {x = etrue}  {y = efalse} e = absurd (etrue≠efalse e)
wk-elit-inj {x = efalse} {y = elit x} e = absurd (elit≠efalse (e ⁻¹))
wk-elit-inj {x = efalse} {y = etrue}  e = absurd (etrue≠efalse (e ⁻¹))
wk-elit-inj {x = efalse} {y = efalse} e = refl

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
              ⊆-maybe z∈)
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

-- duplets & triplets

data Duplet (Γ : LFSet A) : 𝒰 where
  duand : ELit Γ → ELit Γ → Duplet Γ
  duor  : ELit Γ → ELit Γ → Duplet Γ
  -- we never get this
--  duimp : ELit Γ → ELit Γ → Duplet Γ
  duiff : ELit Γ → ELit Γ → Duplet Γ

is-duand : Duplet Γ → 𝒰
is-duand (duand _ _) = ⊤
is-duand  _         = ⊥

is-duor : Duplet Γ → 𝒰
is-duor (duor _ _) = ⊤
is-duor  _        = ⊥

duand≠duor : {p q r s : ELit Γ} → duand p q ≠ duor r s
duand≠duor e = subst is-duand e tt

duand≠duiff : {p q r s : ELit Γ} → duand p q ≠ duiff r s
duand≠duiff e = subst is-duand e tt

duor≠duiff : {p q r s : ELit Γ} → duor p q ≠ duiff r s
duor≠duiff e = subst is-duor e tt

unduplet : Duplet Γ → ELit Γ × ELit Γ
unduplet (duand p q) = p , q
unduplet (duor  p q) = p , q
unduplet (duiff p q) = p , q

duand-inj : {p1 q1 p2 q2 : ELit Γ}
           → duand p1 q1 ＝ duand p2 q2
           → (p1 ＝ p2) × (q1 ＝ q2)
duand-inj = ×-path-inv ∘ ap unduplet

duor-inj : {p1 q1 p2 q2 : ELit Γ}
         → duor p1 q1 ＝ duor p2 q2
         → (p1 ＝ p2) × (q1 ＝ q2)
duor-inj = ×-path-inv ∘ ap unduplet

duiff-inj : {p1 q1 p2 q2 : ELit Γ}
           → duiff p1 q1 ＝ duiff p2 q2
           → (p1 ＝ p2) × (q1 ＝ q2)
duiff-inj = ×-path-inv ∘ ap unduplet

Duplet-= : {Γ : LFSet A}
         → (A → A → Bool)
         → Duplet Γ → Duplet Γ → Bool
Duplet-= e (duand p1 q1) (duand p2 q2) = elit-= e p1 p2 and elit-= e q1 q2
Duplet-= e (duor  p1 q1) (duor  p2 q2) = elit-= e p1 p2 and elit-= e q1 q2
Duplet-= e (duiff p1 q1) (duiff p2 q2) = elit-= e p1 p2 and elit-= e q1 q2
Duplet-= e _              _              = false

Reflects-duplet : {Γ : LFSet A} {e : A → A → Bool}
                → ⦃ r : ∀ {x y} → Reflects (x ＝ y) (e x y) ⦄
                → ∀ {d1 d2} → Reflects (d1 ＝ d2) (Duplet-= {Γ = Γ} e d1 d2)
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
  Duplet-discrete : ⦃ d : is-discrete A ⦄ {Γ : LFSet A}
                  → is-discrete (Duplet Γ)
  Duplet-discrete ⦃ d ⦄ {x} {y} .does  = Duplet-= (λ x y → d .does) x y
  Duplet-discrete ⦃ d ⦄ {x} {y} .proof = Reflects-duplet

wk-duplet : {Γ Δ : LFSet A} → Γ ⊆ Δ → Duplet Γ → Duplet Δ
wk-duplet s (duand x y) = duand (wk-elit s x) (wk-elit s y)
wk-duplet s (duor x y)  = duor (wk-elit s x) (wk-elit s y)
wk-duplet s (duiff x y) = duiff (wk-elit s x) (wk-elit s y)

wk-duplet-inj : {Γ Δ : LFSet A} {s : Γ ⊆ Δ}
              → Injective (wk-duplet s)
wk-duplet-inj {x = duand xa xb} {y = duand ya yb} e =
  let (ex , ey) = duand-inj e in
  ap² duand (wk-elit-inj ex) (wk-elit-inj ey)
wk-duplet-inj {x = duand xa xb} {y = duor ya yb}  e = absurd (duand≠duor e)
wk-duplet-inj {x = duand xa xb} {y = duiff ya yb} e = absurd (duand≠duiff e)
wk-duplet-inj {x = duor xa xb}  {y = duand ya yb} e = absurd (duand≠duor (e ⁻¹))
wk-duplet-inj {x = duor xa xb}  {y = duor ya yb}  e =
  let (ex , ey) = duor-inj e in
  ap² duor (wk-elit-inj ex) (wk-elit-inj ey)
wk-duplet-inj {x = duor xa xb}  {y = duiff ya yb} e = absurd (duor≠duiff e)
wk-duplet-inj {x = duiff xa xb} {y = duand ya yb} e = absurd (duand≠duiff (e ⁻¹))
wk-duplet-inj {x = duiff xa xb} {y = duor ya yb}  e = absurd (duor≠duiff (e ⁻¹))
wk-duplet-inj {x = duiff xa xb} {y = duiff ya yb} e =
  let (ex , ey) = duiff-inj e in
  ap² duiff (wk-elit-inj ex) (wk-elit-inj ey)

duplet→form : Duplet Γ → Formulaᵢ Γ
duplet→form (duand a b) = And (elit→form a) (elit→form b)
duplet→form (duor a b)  = Or (elit→form a) (elit→form b)
duplet→form (duiff a b) = Iff (elit→form a) (elit→form b)

Triplet : LFSet A → 𝒰
Triplet {A} Γ = AVar Γ × Duplet Γ

tripatoms : {Γ : LFSet A}
          → Triplet Γ → List A  -- AVar  ?
tripatoms (av v _ , d) =
  let (l , r) = unduplet d in
  v ∷ Maybe.rec [] ((_∷ []) ∘ unlit) (unelit l) ++ Maybe.rec [] ((_∷ []) ∘ unlit) (unelit r)

