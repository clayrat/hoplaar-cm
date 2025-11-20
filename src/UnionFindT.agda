module UnionFindT where

open import Prelude
open import Meta.Effect hiding (_>>_) renaming (_>>=_ to _>>=ᵐ_)
open import Foundations.Sigma
open import Logic.Discreteness
open Variadics _

open import Data.Unit
open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Two
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Any renaming (Any to Anyₘ)
open import Data.Maybe.Correspondences.Unary.All renaming (All to Allₘ)
open import Data.List
open import Data.List.Operations.Properties
open import Data.List.Operations.Discrete
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Unary.Unique
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


-- partition nodes

data Pnode (A : 𝒰) : 𝒰 where
  nonterminal : A → Pnode A
  terminal    : A → ℕ → Pnode A

nodeval : Pnode A → A
nodeval (nonterminal a) = a
nodeval (terminal a _)  = a

noderank : Pnode A → Maybe ℕ
noderank (nonterminal _) = nothing
noderank (terminal _ n)  = just n

is-nonterminal : Pnode A → 𝒰
is-nonterminal (nonterminal _) = ⊤
is-nonterminal (terminal _ _)  = ⊥

is-nonterminal? : Pnode A → Bool
is-nonterminal? (nonterminal _) = true
is-nonterminal? (terminal _ _)  = false

is-terminal : Pnode A → 𝒰
is-terminal (nonterminal _) = ⊥ 
is-terminal (terminal _ _)  = ⊤

is-terminal? : Pnode A → Bool
is-terminal? = not ∘ is-nonterminal?

Reflects-is-terminal : {x : Pnode A} → Reflects (is-terminal x) (is-terminal? x)
Reflects-is-terminal {x = nonterminal x} = ofⁿ id
Reflects-is-terminal {x = terminal x k}  = ofʸ tt

nonterminal≠terminal : {a b : A} {k : ℕ}
                     → nonterminal a ≠ terminal b k
nonterminal≠terminal p = subst is-nonterminal p tt

nonterminal-inj : {a b : A}
                → nonterminal a ＝ nonterminal b
                → a ＝ b
nonterminal-inj = ap nodeval

terminal-inj : {a b : A} {n m : ℕ}
             → terminal a n ＝ terminal b m
             → (a ＝ b) × (n ＝ m)
terminal-inj e = ap nodeval e , ap (Maybe.rec 0 id ∘ noderank) e

Pnode-= : (A → A → Bool) → Pnode A → Pnode A → Bool
Pnode-= eq (nonterminal x) (nonterminal y) = eq x y
Pnode-= eq (terminal x n)  (terminal y m)  = eq x y and (n == m)
Pnode-= _ _ _ = false

Reflects-Pnode-= : {eq : A → A → Bool}
                   ⦃ r : ∀ {x y} → Reflects (x ＝ y) (eq x y) ⦄
                 → ∀ {x y} → Reflects (x ＝ y) (Pnode-= eq x y)
Reflects-Pnode-= ⦃ r ⦄ {x = nonterminal x} {y = nonterminal y} =
  Reflects.dmap
    (ap nonterminal)
    (contra nonterminal-inj)
    (r {x = x})
Reflects-Pnode-=       {x = nonterminal x} {y = terminal y m}  =
  ofⁿ nonterminal≠terminal
Reflects-Pnode-=       {x = terminal x n}  {y = nonterminal y} =
  ofⁿ (nonterminal≠terminal ∘ _⁻¹)
Reflects-Pnode-= ⦃ r ⦄ {x = terminal x n}  {y = terminal y m}  =
  Reflects.dmap
    ((λ e1 → ap² terminal e1) $²_)
    (contra terminal-inj)
    (Reflects-× ⦃ rp = r {x = x} ⦄ ⦃ rq = Reflects-ℕ-Path {m = n} ⦄ )

instance
  Pnode-discrete : ⦃ d : is-discrete A ⦄
                 → is-discrete (Pnode A)
  Pnode-discrete ⦃ d ⦄ {x} {y} .does = Pnode-= (λ x y → d {x = x} {y = y} .does) x y
  Pnode-discrete .proof = Reflects-Pnode-=

-- partition graph

PGraph : 𝒰 → 𝒰
PGraph A = KVMap A (Pnode A)

-- TODO here we start baking computational maps into properties
-- might be beneficial to have a cofinite map in specs instead?
-- could at least get rid of extra discreteness obligations

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
  let g' = insert-kv b (terminal b k) (g .kv)
    in
    Dec.elim
     {C = λ q → nonterminal y ∈ₘ (if ⌊ q ⌋
                                    then just (nonterminal b)
                                    else lookup-kv g' x)
              → ((x ＝ a) × (y ＝ b)) ⊎ ((x ≠ b) × ntedge g x y)}
     (λ x=a → inl ∘ (x=a ,_) 
            ∘ nonterminal-inj ∘ unhere)
     (λ x≠a → inr
            ∘ subst (λ q → nonterminal y ∈ₘ q → (x ≠ b) × ntedge g x y)
                    (kvlist-insert-lookup {xs = g .kv} x ⁻¹)
                    (Dec.elim
                       {C = λ q → nonterminal y ∈ₘ (if ⌊ q ⌋
                                                      then just (terminal b k)
                                                      else lookup-kv (g .kv) x)
                                → (x ≠ b) × ntedge g x y}
                       (λ x=b en → absurd (nonterminal≠terminal (unhere en)))
                       (λ x≠b → x≠b ,_)
                       (x ≟ b)))
     (x ≟ a)
   ∘ subst (λ q → nonterminal y ∈ₘ q)
           (kvlist-insert-lookup {xs = g'} x)

link-⊆keys : ⦃ d : is-discrete A ⦄
             {a b : A} {k : ℕ}
             {pg : PGraph A}
           → keysm pg ⊆ keysm (link a b k pg)
link-⊆keys {pg} =
    kvlist-upsert-⊆ (Is-kvlist-upsert (pg .inv))
  ∘ kvlist-upsert-⊆ (pg .inv)            

-- TODO?
{-
a∈link-keys : ⦃ d : is-discrete A ⦄
              {a b : A} {k : ℕ}
              {pg : PGraph A}
            → a ∈ keysm (link a b k pg)
a∈link-keys {a} {b} {k} {pg} =
  Dec.rec
    (link-⊆keys {pg = pg})
    (λ a∉ →
      subst (a ∈_)
            (kvlist-upsert-∉-eq (Is-kvlist-upsert (pg .inv))
            (contra {!!} a∉) ⁻¹) $
      any-∷r-last refl)
    (a ∈? keysm pg)
-}

b∈link-keys : ⦃ d : is-discrete A ⦄
              {a b : A} {k : ℕ}
              {pg : PGraph A}
            → b ∈ keysm (link a b k pg)
b∈link-keys {a} {b} {k} {pg} =
  Dec.rec
    (link-⊆keys {pg = pg})
    (λ b∉ →
      kvlist-upsert-⊆ (Is-kvlist-upsert (pg .inv)) $
      subst (b ∈_)
            (kvlist-upsert-∉-eq (pg .inv)
            b∉ ⁻¹) $
      any-∷r-last refl)
    (b ∈? keysm pg)

is-acyclic : ⦃ d : is-discrete A ⦄ → PGraph A → 𝒰
is-acyclic = is-noeth ∘ ntedge

is-closed : ⦃ d : is-discrete A ⦄ → PGraph A → 𝒰
is-closed p = ∀ x y → ntedge p x y → y ∈ keysm p

is-terminus : ⦃ d : is-discrete A ⦄ → PGraph A → A → 𝒰
is-terminus p a = Anyₘ is-terminal (lookupm p a)

is-terminus-opt : ⦃ d : is-discrete A ⦄ → PGraph A → A → 𝒰
is-terminus-opt p a = Allₘ is-terminal (lookupm p a)

link-acyclic : ⦃ d : is-discrete A ⦄
               {a b : A} {k : ℕ}
               {pg : PGraph A}
             → a ≠ b
             → is-acyclic pg
             → is-acyclic (link a b k pg)
link-acyclic {pg} ne acy =
  to-ninduction acy _
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
        ]ᵤ ∘ ntelink {g = pg}
 
link-closed : ⦃ d : is-discrete A ⦄
              {a b : A} {k : ℕ}
              {pg : PGraph A}
            → is-closed pg
            → is-closed (link a b k pg)
link-closed {a} {b} {k} {pg} clo x y =
  [ (λ where
        (_ , y=b) →
           subst (_∈ keysm (link a b k pg))
                 (y=b ⁻¹)
                 (b∈link-keys {pg = pg}))
  , (λ where
        (_ , ed) →
           link-⊆keys {pg = pg} $ clo x y ed)
  ]ᵤ ∘ ntelink {g = pg}

terminus-opt→terminus : ⦃ d : is-discrete A ⦄
                      → {p : PGraph A} {a : A}
                      → a ∈ keysm p
                      → is-terminus-opt p a
                      → is-terminus p a
terminus-opt→terminus {p} a∈ to =
  let (v , _ , v∈) = lookup←has (p .inv) a∈ in
  Maybe.∈→Any v∈ $ Maybe.All→∀∈ to v v∈

record Partition (A : 𝒰) ⦃ d : is-discrete A ⦄ : 𝒰 where
  constructor mkpartition
  field
    pg  : PGraph A
    acy : is-acyclic pg
    clo : is-closed pg

open Partition public

pg-injective : ⦃ d : is-discrete A ⦄ → Injective (pg {A = A})
pg-injective {x = mkpartition pgx acyx clox} {y = mkpartition pgy acyy cloy} e =
  ap² {B = λ pg → is-acyclic pg × is-closed pg}
    (λ x (ea , ac) → mkpartition x ea ac)
    e
    (to-pathᴾ (×-path ((Π-is-of-hlevel 1 λ x → hlevel 1) _ acyy)
                      ((Π-is-of-hlevel 1 λ x → Π-is-of-hlevel 1 λ y → fun-is-of-hlevel 1 $
                        Uniq-set→is-unique (is-discrete→is-set auto) (pgy .inv) y) _ cloy)))

instance
  Partition-discrete : ⦃ d : is-discrete A ⦄
                     → is-discrete (Partition A)
  Partition-discrete ⦃ d ⦄ = ↣→is-discrete (pg , pg-injective) auto

equated : ⦃ d : is-discrete A ⦄
        → Partition A → List A
equated (mkpartition pg _ _) = keysm pg

terminus-loop : ⦃ d : is-discrete A ⦄
                (pg : PGraph A)
              → is-closed pg
              → (x : A) 
              → ((y : A) → ntedge pg x y → y ∈ keysm pg → Σ[ a ꞉ A ] is-terminus pg a × ℕ)
              → x ∈ keysm pg              
              → Σ[ a ꞉ A ] is-terminus pg a × ℕ
terminus-loop {A} pg cl x ih x∈ =
  Maybe.elim
    (λ m → lookupm pg x ＝ m → Σ[ a ꞉ A ] is-terminus pg a × ℕ)
    (λ n → absurd (lookup→∉ (pg .inv) n x∈))
    (λ where
         (nonterminal z) e →
            let e' = =just→∈ e in
            ih z e' (cl x z e')
         (terminal z n) e → x , subst (λ q → Anyₘ is-terminal q) (e ⁻¹) (here tt) , n)
    (lookupm pg x) refl

terminus : ⦃ d : is-discrete A ⦄
         → (p : Partition A) → A
         → Σ[ a ꞉ A ] is-terminus-opt (p .pg) a × ℕ
terminus {A} (mkpartition pg acy clo) x =
  Maybe.elim
    (λ m → lookupm pg x ＝ m → Σ[ a ꞉ A ] is-terminus-opt pg a × ℕ)
    (λ n → x , subst (λ q → Allₘ is-terminal q) (n ⁻¹) nothing , 1)
    (λ where
         (nonterminal z) e →
            let xon = to-ninduction acy
                        (λ z → z ∈ keysm pg → Σ[ a ꞉ A ] (is-terminus pg a × ℕ))
                        (terminus-loop pg clo)
                        x (lookup→has (=just→∈ e))
             in
            xon .fst , any→all (xon .snd .fst) , xon .snd .snd
         (terminal z n) e → x , subst (λ q → Allₘ is-terminal q) (e ⁻¹) (just tt) , n)
    (lookupm pg x) refl

join : ⦃ d : is-discrete A ⦄
     → (a b : A)
     → a ≠ b
     → ℕ
     → Partition A
     → Partition A
join a b ne k (mkpartition pg acy clo) =
  mkpartition
    (link a b k pg)
    (link-acyclic {pg = pg} ne acy)
    (link-closed {pg = pg} clo)

equate-neq : ⦃ d : is-discrete A ⦄
           → (a b : A)
           → a ≠ b
           → ℕ → ℕ
           → Partition A
           → Partition A
equate-neq a b ne na nb p =
  if na ≤? nb
    then join a b  ne        (na + nb) p
    else join b a (ne ∘ _⁻¹) (na + nb) p

-- API (+ equated)

unequal : ⦃ d : is-discrete A ⦄
        → Partition A
unequal = mkpartition emptym (λ x → acc λ y → false!) λ x y → false!

canonize : ⦃ d : is-discrete A ⦄
         → Partition A → A → A
canonize eqv = fst ∘ terminus eqv

equivalent : ⦃ d : is-discrete A ⦄
           → Partition A → A → A → Bool
equivalent eqv a b = canonize eqv a =? canonize eqv b

equate : ⦃ d : is-discrete A ⦄
       → A → A → Partition A → Partition A
equate a b p =
  let (a' , ta , na) = terminus p a
      (b' , tb , nb) = terminus p b
    in
  Dec.rec
    (λ _ → p)
    (λ ne → equate-neq a' b' ne na nb p)
    (a' ≟ b')

-- properties

partition-size : ⦃ d : is-discrete A ⦄
               → Partition A → A → ℕ
partition-size eqv = snd ∘ snd ∘ terminus eqv

nonterminals : ⦃ d : is-discrete A ⦄
             → Partition A → ℕ
nonterminals (mkpartition pg _ _) = count is-nonterminal? $ valsm pg

is-nonterminal-opt? : Maybe (Pnode A) → Bool
is-nonterminal-opt? = Maybe.rec false is-nonterminal?

nonterm≤ : ⦃ d : is-discrete A ⦄
         → {p : Partition A}
         → nonterminals p ≤ length (equated p)
nonterm≤ {p} =
    count≤length is-nonterminal? (valsm (p .pg))
  ∙ =→≤ (map-length ∙ map-length ⁻¹)         

canonize-terminal : ⦃ d : is-discrete A ⦄ 
                  → {p : Partition A} {a : A}
                  → is-terminus-opt (p .pg) (canonize p a)
canonize-terminal {p} {a} = fst $ snd $ terminus p a

-- TODO next 3 are messy / lotta copypaste
lookup-link-implies : ⦃ d : is-discrete A ⦄ 
                    → {p : Partition A} {a b : A} {k : ℕ}
                    → (bt : is-terminus-opt (p .pg) b)
                    → {x : A}
                    → x ∈ keysm (p .pg)
                    →  ⌞ is-nonterminal-opt? (lookupm (            p .pg ) x)
                         implies
                         is-nonterminal-opt? (lookupm (link a b k (p .pg)) x) ⌟
lookup-link-implies {p} {a} {b} {k} bt {x} x∈ =
  true→so! ⦃ reflects-implies ⦄ $
  λ mr →
    subst (So ∘ is-nonterminal-opt?)
          (kvlist-insert-lookup
             {k = a} {v = nonterminal b}
             {xs = insert-kv _ _ (p .pg .kv)}
             x ⁻¹) $
    let pbx = lookup-kv (insert-kv b (terminal b k) (p .pg .kv)) x
        px = lookup-kv (p .pg .kv) x
      in
    Dec.elim
      {C = λ q → So (is-nonterminal-opt?
                       (if ⌊ q ⌋
                          then just (nonterminal b)
                          else pbx))}
      (λ x=a → oh)
      (λ x≠a →
          subst (So ∘ is-nonterminal-opt?)
             (kvlist-insert-lookup
               {k = b} {v = terminal b k}
               {xs = p .pg .kv}
               x ⁻¹) $
          Dec.elim
            {C = λ q → So (is-nonterminal-opt?
                             (if ⌊ q ⌋
                                then just (terminal b k)
                                else px))}
             (λ x=b →
                let (v , v∈ , ve) = Maybe.Any→Σ∈ (terminus-opt→terminus {p = p . pg} x∈
                                      (subst (is-terminus-opt (p .pg)) (x=b ⁻¹) bt))
                  in
                absurd (so-not (subst So (not-invol (is-nonterminal? v) ⁻¹) $
                                subst (So ∘ is-nonterminal-opt?) (∈→=just v∈) mr) $
                        true→so! ⦃ Reflects-is-terminal ⦄ ve))
             (λ x≠b → mr)
             (x ≟ b))
      (x ≟ a)

join-nonterminals : ⦃ d : is-discrete A ⦄ 
                  → {p : Partition A} {a b : A} {k : ℕ}
                  → (ne : a ≠ b)
                  → is-terminus-opt (p .pg) a 
                  → is-terminus-opt (p .pg) b
                  → nonterminals p < nonterminals (join a b ne k p)
join-nonterminals ⦃ d ⦄ {p} {a} {b} {k} ne at bt =
  ≤-<-trans
    (=→≤ (  ap (count is-nonterminal?)
               (values-lookup (p .pg .inv))
          ∙ count-map-maybe {xs = keysm (p .pg)}))
    (<-≤-trans
       (Dec.rec
          (λ a∈ →
             <-≤-trans
               (count-<-implies
                  (lookup-link-implies {p = p} bt)
                  (  a , a∈
                   , not-so (λ s →
                       let (v , v∈ , ve) = Maybe.Any→Σ∈ (terminus-opt→terminus {p = p . pg} a∈ at) in
                       so-not
                         (subst So (not-invol (is-nonterminal? v) ⁻¹) $
                          subst (So ∘ is-nonterminal-opt?) (∈→=just v∈) s) $
                       true→so! ⦃ Reflects-is-terminal ⦄ ve)
                   , subst (So ∘ is-nonterminal-opt?)
                           (  if-true (true→so! ⦃ d .proof ⦄ refl) ⁻¹
                            ∙ kvlist-insert-lookup {xs = insert-kv _ _ (p .pg .kv)} a ⁻¹)
                           oh))
               (=→≤ $
                Dec.rec
                  (λ b∈ → ap (count (is-nonterminal-opt? ∘ lookup-kv (link a b k (p .pg) .kv)))
                             (let beq = kvlist-upsert-∈-eq (p .pg .inv) b∈ ⁻¹ in 
                                 beq
                               ∙ kvlist-upsert-∈-eq (Is-kvlist-upsert (p .pg .inv))
                                                    (subst (a ∈_) beq a∈) ⁻¹))
                  (λ b∉ →   +-zero-r _ ⁻¹
                          ∙ ap (λ q → count (is-nonterminal-opt? ∘ lookup-kv (link a b k (p .pg) .kv)) (keysm (p .pg))
                                      + bit (is-nonterminal-opt? q))
                               (  if-true (true→so! ⦃ d .proof ⦄ refl) ⁻¹
                                ∙ kvlist-insert-lookup {xs = p .pg .kv} b ⁻¹
                                ∙ if-false (false→so! (ne ∘ _⁻¹)) ⁻¹
                                ∙ kvlist-insert-lookup {xs = insert-kv _ _ (p .pg .kv)} b ⁻¹)
                          ∙ count-∷r _ (keys (p .pg .kv)) b ⁻¹
                          ∙ ap (count (is-nonterminal-opt? ∘ lookup-kv (link a b k (p .pg) .kv)))
                               (let beq = kvlist-upsert-∉-eq {f = λ _ x → x} {v = terminal b k} (p .pg .inv) b∉ ⁻¹ in 
                                 beq
                                ∙ kvlist-upsert-∈-eq (Is-kvlist-upsert (p .pg .inv))
                                                     (subst (a ∈_) beq (any-∷r-init a∈)) ⁻¹))
                  (b ∈? keysm (p .pg))))
          (λ a∉ →
             <-≤-trans
               (≤≃<suc $
                count-≤-implies
                  (lookup-link-implies {p = p} bt))
               (=→≤ $
                Dec.rec
                  (λ b∈ →   +-comm 1 _
                          ∙ ap (λ q → count (is-nonterminal-opt? ∘ lookup-kv (link a b k (p .pg) .kv)) (keysm (p .pg))
                                      + bit (is-nonterminal-opt? q))
                               (  if-true (true→so! ⦃ d .proof ⦄ refl) ⁻¹
                                ∙ kvlist-insert-lookup {xs = insert-kv _ _ (p .pg .kv)} a ⁻¹)
                          ∙ count-∷r _ (keys (p .pg .kv)) a ⁻¹
                          ∙ ap (count (is-nonterminal-opt? ∘ lookup-kv (link a b k (p .pg) .kv)))
                               (let beq = kvlist-upsert-∈-eq (p .pg .inv) b∈ ⁻¹ in 
                                  ap (_∷r a) beq
                                ∙ kvlist-upsert-∉-eq {f = λ _ x → x} {v = nonterminal b}
                                     (Is-kvlist-upsert (p .pg .inv))
                                     (subst (a ∉_) beq a∉) ⁻¹))
                  (λ b∉ →   ap suc
                               (  +-zero-r _ ⁻¹
                                ∙ ap (λ q → count (is-nonterminal-opt? ∘ lookup-kv (link a b k (p .pg) .kv)) (keysm (p .pg))
                                            + bit (is-nonterminal-opt? q))
                                     (  if-true (true→so! ⦃ d .proof ⦄ refl) ⁻¹
                                      ∙ kvlist-insert-lookup {xs = p .pg .kv} b ⁻¹
                                      ∙ if-false (false→so! (ne ∘ _⁻¹)) ⁻¹
                                      ∙ kvlist-insert-lookup {xs = insert-kv _ _ (p .pg .kv)} b ⁻¹))
                          ∙ +-comm 1 _
                          ∙ ap (λ q → count (is-nonterminal-opt? ∘ lookup-kv (link a b k (p .pg) .kv)) (keysm (p .pg))
                                      + bit (is-nonterminal-opt? (lookup-kv (link a b k (p .pg) .kv) b))
                                      + bit (is-nonterminal-opt? q))
                               (  if-true (true→so! ⦃ d .proof ⦄ refl) ⁻¹
                                ∙ kvlist-insert-lookup {xs = insert-kv _ _ (p .pg .kv)} a ⁻¹)
                          ∙ ap (_+ bit (is-nonterminal-opt? (lookup-kv (link a b k (p .pg) .kv) a)))
                               (count-∷r _ (keys (p .pg .kv)) b ⁻¹)
                          ∙ count-∷r _ (keys (p .pg .kv) ∷r b) a ⁻¹
                          ∙ ap (count (is-nonterminal-opt? ∘ lookup-kv (link a b k (p .pg) .kv)))
                               (let beq = kvlist-upsert-∉-eq {f = λ _ x → x} {v = terminal b k} (p .pg .inv) b∉ ⁻¹ in
                                   ap (_∷r a) beq
                                 ∙ kvlist-upsert-∉-eq {f = λ _ x → x} {v = nonterminal b}
                                     (Is-kvlist-upsert (p .pg .inv))
                                     (subst (a ∉_) beq
                                        (¬any-∷r a∉ ne)) ⁻¹))
                  (b ∈? keysm (p .pg))))
          (a ∈? keysm (p .pg)))
       (=→≤ (  count-map-maybe {xs = keysm (link a b k (p .pg))} ⁻¹
             ∙ ap (count is-nonterminal?)
                  (values-lookup (Is-kvlist-upsert (Is-kvlist-upsert (p .pg .inv)))) ⁻¹)))

equate-nonterminals : ⦃ d : is-discrete A ⦄ 
                    → {p : Partition A} {a b : A}
                    → ⌞ not (equivalent p a b) ⌟
                    → nonterminals p < nonterminals (equate a b p)
equate-nonterminals {p} {a} {b} neq =
  given-no so→false! neq
     return (λ q → nonterminals p < nonterminals (Dec.rec (λ _ → p)
                                                    (λ ne → equate-neq (canonize p a)
                                                                       (canonize p b)
                                                                       ne
                                                                       (partition-size p a)
                                                                       (partition-size p b)
                                                                       p)
                                                    q))
     then
       the (nonterminals p < nonterminals (equate-neq (canonize p a)
                                                      (canonize p b)
                                                      (so→false! neq)
                                                      (partition-size p a)
                                                      (partition-size p b)
                                                      p)) 
       (Dec.elim
         {C = λ q → nonterminals p < nonterminals (if ⌊ q ⌋
                                                    then join (canonize p a) (canonize p b) (so→false! neq)
                                                              (partition-size p a + partition-size p b) p
                                                    else join (canonize p b) (canonize p a) (so→false! neq ∘ _⁻¹)
                                                              (partition-size p a + partition-size p b) p)}
         (λ pa≤pb → join-nonterminals {p = p} {k = partition-size p a + partition-size p b}
                      (so→false! neq)
                      (canonize-terminal {p = p} {a = a})
                      (canonize-terminal {p = p} {a = b}))
         (λ pb<pa → join-nonterminals {p = p} {k = partition-size p a + partition-size p b}
                      (so→false! neq ∘ _⁻¹)
                      (canonize-terminal {p = p} {a = b})
                      (canonize-terminal {p = p} {a = a}))
         (≤-dec {x = partition-size p a} {x = partition-size p b}))
