module ch2.Ix.DP where

open import Prelude
open Variadics _
open import Meta.Show
open import Meta.Effect hiding (_>>_) renaming (_>>=_ to _>>=ᵐ_)
open import Meta.Effect.Bind.State
open import Logic.Discreteness
open import System.Everything hiding (_<$>_)

open import Data.Unit
open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects
open import Data.Reflects.Sigma as ReflectsΣ
open import Data.Dec as Dec
open import Data.Dec.Sigma as DecΣ
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.List as List renaming (has to hasₗ)
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Operations.Properties as List
open import Data.List.Operations.Rel
open import Data.List.Operations.Discrete renaming (rem to remₗ)
open import Data.Sum
open import Data.String

open import Order.Diagram.Meet
open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open decminmax ℕ-dec-total

open import Induction.Nat.Strong as Box using (□_)

open import Data.List.NonEmpty as List⁺

open import ListSet

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
open import ch2.Ix.DPCore

private variable
  A : 𝒰
  v : Var
  Γ : Ctx

-- induction on context size
DP-ty : ℕ → 𝒰
DP-ty x = {Γ : Ctx} → x ＝ sizeₛ Γ
                     → CNF Γ → Bool

dp-loop : ∀[ □ DP-ty ⇒ DP-ty ]
dp-loop ih {Γ} e c =
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
                               let (l , rc) = resolution-rule c
                                                (true→so! ⦃ Reflects-any-bool ⦄
                                                  (resolution-pos c ((λ {l} → pn {l})) cn nc))
                                 in
                               Box.call ih
                                 (<-≤-trans
                                    (<-≤-trans
                                       (≤≃<suc $ ≤-refl)
                                       (=→≤ (rem-size-∈ (unlit∈ l) ⁻¹)))
                                    (=→≤ (e ⁻¹)))
                                 refl rc)
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

dp : CNF Γ → Bool
dp = Box.fix DP-ty dp-loop refl

dpsat : Formulaᵢ Γ → Bool
dpsat = dp ∘ snd ∘ defcnfs

dptaut : Formulaᵢ Γ → Bool
dptaut = not ∘ dpsat ∘ Not

{-
main : Main
main =
  run $
  do -- put-str-ln $ "prime 11  : " ++ₛ (show $ tautology $ prime 11)
     put-str-ln $ "prime(DP) 16: " ++ₛ ppFBᵢ dptaut (prime 16)
--     put-str-ln $ "prime 13DP: " ++ₛ ppFBᵢ dptaut (prime 13)
--     put-str-ln $ "prime 17DP: " ++ₛ ppFBᵢ dptaut (prime 17)
-}
