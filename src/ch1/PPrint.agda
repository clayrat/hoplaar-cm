module ch1.PPrint where

open import Foundations.Prelude
open import Meta.Effect

open import Data.Bool
open import Data.List as List
open import Data.Char
open import Data.String
open import Data.Nat
open import Data.Maybe as Maybe

open import Text.Pretty 80

open import ch1.Expr

prettyExpr : ℕ → Expr → Doc
prettyExpr _ (Var v)   = text v
prettyExpr _ (Const n) = text $ show-ℕ n
prettyExpr p (Add x y) =
  let s = sep ((prettyExpr 3 x ◈ text "+") ∷ prettyExpr 2 y ∷ []) in
  if 2 <? p then parens s else s
prettyExpr p (Mul x y) =
  let s = sep ((prettyExpr 5 x ◈ text "*") ∷ prettyExpr 4 y ∷ []) in
  if 4 <? p then parens s else s

pretty : Expr → String
pretty = render ∘ prettyExpr 0

_ : pretty (Add (Var "x") (Mul (Const 3) (Var "y"))) ＝ "x + 3 * y"
_ = refl

_ : pretty (Mul (Add (Var "x") (Const 3)) (Var "y")) ＝ "(x + 3) * y"
_ = refl

_ : pretty (Add (Const 1) (Add (Const 2) (Const 3))) ＝ "1 + 2 + 3"
_ = refl

_ : pretty (Add (Add (Add (Const 1) (Const 2)) (Const 3)) (Const 4)) ＝ "((1 + 2) + 3) + 4"
_ = refl

bigsum : String → ℕ → Expr
bigsum v u = List.rec (Var (v ++ₛ show-ℕ u))
                      (λ n → Add (Var (v ++ₛ show-ℕ n)))
                      (count-from-to 1 u)

big : Expr
big = Mul (bigsum "x" 10) (bigsum "y" 10)

-- _ : pretty big ＝ "(x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10) *
-- \                 \(y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 + y9 + y10)"
-- _ = refl

