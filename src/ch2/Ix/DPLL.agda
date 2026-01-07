{-# OPTIONS --no-exact-split #-}
module ch2.Ix.DPLL where

open import Prelude
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
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Unary.Unique
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Operations.Properties as List
open import Data.List.Operations.Rel
open import Data.List.Operations.Discrete renaming (rem to remₗ)
open import Data.List.Instances.Map.Properties
open import Data.Sum
open import Data.String

open import Order.Diagram.Meet
open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open decminmax ℕ-dec-total

open import Induction.Nat.Strong as Box using (□_)

open import Data.List.NonEmpty as List⁺

open import ListSet
open import KVMapU

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete as LFSet

open import ch2.Formula using (Var)
open import ch2.Appl
open import ch2.Ix.Formula
-- open import ch2.Ix.Sem
open import ch2.Ix.Lit
open import ch2.Ix.NF
open import ch2.Ix.CNF
open import ch2.Ix.DPCore

private variable
  A : 𝒰
  v : Var
  Γ Δ Ξ : Ctx

open KVOps
open KVOps2

-- induction on context size, identical to DP
DPLL-ty : ℕ → 𝒰
DPLL-ty x = {Γ : Ctx} → x ＝ sizeₛ Γ
                      → CNF Γ → Bool

dpll-loop : ∀[ □ DPLL-ty ⇒ DPLL-ty ]
dpll-loop ih {Γ} e c =
  Dec.rec
    (λ _ → true)
    (λ cn → Dec.rec
              (λ _ → false)
              (λ nc → Maybe.rec
                        ([ (λ where (Δ , (z , z∈Δ , z∈Γ) , c′) →
                                       Box.call ih
                                         (<-≤-trans
                                             (<-≤-trans
                                               (<-≤-trans
                                                 (<-+-0lr (size-∈->0 (∈-∩∷← z∈Γ z∈Δ)))
                                                 (=→≤ (+-comm (sizeₛ _) (sizeₛ _))))
                                               (=→≤ (size-minus-∩∷ {ys = Δ})))
                                             (=→≤ (e ⁻¹)))
                                         refl c′)
                         , (λ pn →
                               let l = splitting-rule c
                                         (true→so! ⦃ Reflects-any-bool ⦄
                                           (resolution-pos c ((λ {l} → pn {l})) cn nc))
                                 in
                              Box.call ih
                                (<-≤-trans
                                   (<-≤-trans
                                      (≤≃<suc $ ≤-refl)
                                      (=→≤ (rem-size-∈ (unlit∈ l) ⁻¹)))
                                   (=→≤ (e ⁻¹)))
                                refl (unit-propagate l c)
                                or
                              Box.call ih
                                ((<-≤-trans
                                   (<-≤-trans
                                      (≤≃<suc $ ≤-refl)
                                      (=→≤ (rem-size-∈ (subst (_∈ Γ) (unlit-negate {x = l}) (unlit∈ l)) ⁻¹)))
                                   (=→≤ (e ⁻¹))))
                                refl (unit-propagate (negate l) c))
                         ]ᵤ (affirmative-negative-rule c))
                        (λ where (l , c′) →
                                    Box.call ih
                                      (<-≤-trans
                                         (<-≤-trans
                                            (≤≃<suc $ ≤-refl)
                                            (=→≤ (rem-size-∈ (unlit∈ l) ⁻¹)))
                                         (=→≤ (e ⁻¹)))
                                      refl c′)
                        (one-lit-rule c))
              ([] ∈? c))
    (Dec-is-nil? c)

dpll : CNF Γ → Bool
dpll = Box.fix DPLL-ty dpll-loop refl

dpllsat : Formulaᵢ Γ → Bool
dpllsat = dpll ∘ snd ∘ defcnfs

dplltaut : Formulaᵢ Γ → Bool
dplltaut = not ∘ dpllsat ∘ Not

{-
main : Main
main =
  run $
  do -- put-str-ln $ "prime 11      : " ++ₛ (show $ tautology $ prime 11)
--     put-str-ln $ "prime(DPLL) 13: " ++ₛ ppFBᵢ dplltaut (prime 13)
--     put-str-ln $ "prime(DPLL) 16: " ++ₛ ppFBᵢ dplltaut (prime 16)
--     put-str-ln $ "prime(DPLL) 17: " ++ₛ ppFBᵢ dplltaut (prime 17)
     put-str-ln $ "prime(DPLL) 21: " ++ₛ ppFBᵢ dplltaut (prime 21)
-}
