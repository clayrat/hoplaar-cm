module UnionFindT where

open import Foundations.Prelude
open import Logic.Discreteness
open Variadics _

open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Any renaming (Any to Anyₘ)
open import Data.List
open import Data.List.Operations.Discrete
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Binary.Perm
open import Data.Sum
open import Data.Acc

open import KVListU
open import KVMapU

private variable
  A : 𝒰

open KVListU.Ops
open KVOps
open KVOps2

data Pnode (A : 𝒰) : 𝒰 where
  nonterminal : A → Pnode A
  terminal    : A → ℕ → Pnode A

nodeval : Pnode A → A
nodeval (nonterminal a) = a
nodeval (terminal a _)  = a

is-nonterminal : Pnode A → 𝒰
is-nonterminal (nonterminal _) = ⊤
is-nonterminal (terminal _ _) = ⊥

nonterminal≠terminal : {a b : A} {k : ℕ}
                     → nonterminal a ≠ terminal b k
nonterminal≠terminal p = subst is-nonterminal p tt

nonterminal-inj : {a b : A}
                → nonterminal a ＝ nonterminal b
                → a ＝ b
nonterminal-inj = ap nodeval

PGraph : 𝒰 → 𝒰
PGraph A = KVMap A (Pnode A)

ntedge : ⦃ d : is-discrete A ⦄ → PGraph A → A → A → 𝒰
ntedge g x y = nonterminal y ∈ₘ lookupm g x

link : ⦃ d : is-discrete A ⦄
     → A → A → ℕ
     → PGraph A
     → PGraph A
link a b n = insertm a (nonterminal b) ∘ insertm b (terminal b n)

-- a nonterminal edge in a linked graph
-- either goes from a to b
-- or falls back to the original graph
ntelink : ⦃ d : is-discrete A ⦄
        → {a b : A} {k : ℕ} {g : PGraph A}
          {x y : A}
        → ntedge (link a b k g) x y
        → ((x ＝ a) × (y ＝ b)) ⊎ ((x ≠ b) × ntedge g x y)
ntelink {a} {b} {k} {g} {x} {y} =
  let g' = upsert-kv (λ _ → id) b (terminal b k) (g .kv)
    in
    Dec.elim
     {C = λ q → nonterminal y ∈ₘ (if ⌊ q ⌋
                                    then Maybe.rec
                                           (just (nonterminal b))
                                           (λ _ → just (nonterminal b))
                                           (lookup-kv g' x)
                                    else lookup-kv g' x)
              → ((x ＝ a) × (y ＝ b)) ⊎ ((x ≠ b) × ntedge g x y)}
     (λ x=a → inl ∘ (x=a ,_)
            ∘ subst (λ q → nonterminal y ∈ₘ q → y ＝ b)
                    (rec-fusion {z = b} {f = nodeval} {g = λ _ → just (nonterminal b)}
                       (lookup-kv g' x))
                    (nonterminal-inj ∘ unhere))
     (λ x≠a → inr
            ∘ subst (λ q → nonterminal y ∈ₘ q → (x ≠ b) × ntedge g x y)
                    (kvlist-upsert-lookup {xs = g .kv} x ⁻¹)
                    (Dec.elim
                       {C = λ q → nonterminal y ∈ₘ (if ⌊ q ⌋
                                                      then Maybe.rec
                                                             (just (terminal b k))
                                                             (λ _ → just (terminal b k))
                                                             (lookup-kv (g .kv) x)
                                                      else lookup-kv (g .kv) x)
                                → (x ≠ b) × ntedge g x y}
                       (λ x=b → subst (λ q → nonterminal y ∈ₘ q → (x ≠ b) × ntedge g x y)
                                      (rec-fusion {z = b} {f = nodeval} {g = λ _ → just (terminal b k)}
                                         (lookup-kv (g .kv) x))
                                      λ en → absurd (nonterminal≠terminal (unhere en)))
                       (λ x≠b → x≠b ,_)
                       (x ≟ b)))
     (x ≟ a)
   ∘ subst (λ q → nonterminal y ∈ₘ q)
           (kvlist-upsert-lookup {xs = g'} x)

is-acyclic : ⦃ d : is-discrete A ⦄ → PGraph A → 𝒰
is-acyclic = is-noeth ∘ ntedge

record Partition (A : 𝒰) ⦃ d : is-discrete A ⦄ : 𝒰 where
  constructor mkpartition
  field
    pg  : PGraph A
    acy : is-acyclic pg

open Partition public

terminus-loop : ⦃ d : is-discrete A ⦄
                (pg : KVMap A (Pnode A))
              → (x : A)
              → ((y : A) → ntedge pg x y → Maybe (A × ℕ))
              → Maybe (A × ℕ)
terminus-loop {A} pg x ih =
  Maybe.elim
    (λ m → lookupm pg x ＝ m → Maybe (A × ℕ))
    (λ _ → nothing)
    (λ where
         (nonterminal z) e → ih z (=just→∈ e)
         (terminal z n) _ → just (z , n))
    (lookupm pg x) refl

terminus : ⦃ d : is-discrete A ⦄
         → Partition A → A → Maybe (A × ℕ)
terminus {A} (mkpartition pg acy) = to-ninduction acy _ (terminus-loop pg)

try-terminus : ⦃ d : is-discrete A ⦄
             → Partition A → A → A × ℕ
try-terminus p a =
  Maybe.rec
    (a , 1)
    id
    (terminus p a)

canonize : ⦃ d : is-discrete A ⦄
         → Partition A → A → A
canonize eqv = fst ∘ try-terminus eqv

equivalent : ⦃ d : is-discrete A ⦄
           → Partition A → A → A → Bool
equivalent eqv a b = canonize eqv a =? canonize eqv b

join : ⦃ d : is-discrete A ⦄
     → (a b : A)
     → a ≠ b
     → ℕ
     → (p : Partition A)
     → Partition A
join a b ne k (mkpartition pg acy) =
  mkpartition
    (link a b k pg)
    (to-ninduction acy _
        λ x ih → acc λ y →
           [ (λ where
                  (_ , y=b) → acc λ z →
                     [ (λ where
                           (y=a , _) → absurd (ne (y=a ⁻¹ ∙ y=b)))
                     , (λ where
                           (y≠b , _) → absurd (y≠b y=b))
                     ]ᵤ ∘ ntelink {g = pg})
           , (λ where
                  (_ , e′) → ih y e′)
           ]ᵤ ∘ ntelink {g = pg})

equate : ⦃ d : is-discrete A ⦄
       → A → A → Partition A → Partition A
equate a b p =
  let (a' , na) = try-terminus p a
      (b' , nb) = try-terminus p b
    in
  Dec.rec
    (λ _ → p)
    (λ ne →
         if na ≤? nb
             then join a' b'  ne        (na + nb) p
             else join b' a' (ne ∘ _⁻¹) (na + nb) p)
    (a' ≟ b')

unequal : ⦃ d : is-discrete A ⦄
        → Partition A
unequal = mkpartition emptym (λ x → acc λ y → false!)

equated : ⦃ d : is-discrete A ⦄
        → Partition A → List A
equated (mkpartition pg _) = keysm pg
