{-# OPTIONS --safe #-}
module ch1.Expr where

open import Foundations.Prelude
open import Data.Nat
open import Data.String

data Expr : 𝒰 where
  Var   : String → Expr
  Const : ℕ → Expr
  Add   : Expr → Expr → Expr
  Mul   : Expr → Expr → Expr

simplify1 : Expr → Expr
simplify1 (Add (Const m) (Const n)) = Const (m + n)
simplify1 (Mul (Const m) (Const n)) = Const (m · n)
simplify1 (Add (Const 0)  e)        = e
simplify1 (Add e         (Const 0)) = e
simplify1 (Mul (Const 0)  _)        = Const 0
simplify1 (Mul _         (Const 0)) = Const 0
simplify1 (Mul (Const 1)  e)        = e
simplify1 (Mul e         (Const 1)) = e
simplify1 e                         = e

simplify : Expr → Expr
simplify (Add e₁ e₂) = simplify1 (Add (simplify e₁) (simplify e₂))
simplify (Mul e₁ e₂) = simplify1 (Mul (simplify e₁) (simplify e₂))
simplify e = simplify1 e

testexpr : Expr
testexpr = Add (Mul (Add (Mul (Const 0)
                              (Var "x"))
                         (Const 1))
                    (Const 3))
               (Const 12)

test : simplify testexpr ＝ Const 15
test = refl
