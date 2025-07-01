module ch1.Parse where

open import Foundations.Prelude
open import Meta.Effect

open import Data.List
open import Data.Char
open import Data.String
open import Data.Maybe as Maybe

open import Data.List.NonEmpty as List⁺
open import Data.List.Sized.Interface as SZ
import Induction.Nat.Strong as INS
open import Level.Bounded

open import Base 0ℓ
open import ch1.Expr

record PExpr (P : Parameters 0ℓ) (n : ℕ) : 𝒰 (Effect.adj (Parameters.M P) 0ℓ) where
  field pvar : Parser P (Expr 0↑ℓ) n
        pcst : Parser P (Expr 0↑ℓ) n
        pfac : Parser P (Expr 0↑ℓ) n
        pexp : Parser P (Expr 0↑ℓ) n
open PExpr

ch : Parameters 0ℓ
ch = chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄

pExpr : ∀[ PExpr ch ]
pExpr = INS.fix (PExpr ch) $
        λ rec →
        let factor = parens (INS.map pexp rec) <|>C var <|>C cst
            term   = chainr1 factor $ box mulop
            expr   = chainr1 term   $ box addop
        in record { pvar = var
                  ; pcst = cst
                  ; pfac = factor
                  ; pexp = expr }

 module Details where
   instance _ = Bind-Id

   var : ∀[ Parser ch (Expr 0↑ℓ) ]
   var {x} = (λ where (s , mb) →
                         Var $ list→string $ List⁺.to-list $
                         s ⁺++ Maybe.rec [] List⁺.to-list mb)
              <$>C (alphas⁺ <&?> box (list⁺ num))

   cst : ∀[ Parser ch (Expr 0↑ℓ) ]
   cst {x} = Const <$>C decimalℕ

   addop : ∀[ Parser ch ((Expr 0↑ℓ) →ℓ ((Expr 0↑ℓ) →ℓ (Expr 0↑ℓ)))]
   addop {x} = withSpaces (Add <$C char '+')

   mulop : ∀[ Parser ch ((Expr 0↑ℓ) →ℓ ((Expr 0↑ℓ) →ℓ (Expr 0↑ℓ)))]
   mulop {x} = withSpaces (Mul <$C char '*')

ExprP : ∀[ Parser ch (Expr 0↑ℓ) ]
ExprP {x} = pexp pExpr

-- tests

_ : _∈P_ {P = ch} ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "x + 1"
         ExprP
_ = Add (Var "x") (Const 1) !

_ : _∈P_ {P = ch} ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "1 + 2 + 3"
         ExprP
_ = Add (Const 1) (Add (Const 2) (Const 3)) !

_ : _∈P_ {P = ch} ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "((1 + 2) + 3) + 4"
         ExprP
_ = Add (Add (Add (Const 1) (Const 2)) (Const 3)) (Const 4) !

_ : _∈P_ {P = ch} ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "x + 3 * y"
         ExprP
_ = Add (Var "x") (Mul (Const 3) (Var "y")) !

_ : _∈P_ {P = ch} ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "(x + 3) * y"
         ExprP
_ = Mul (Add (Var "x") (Const 3)) (Var "y") !

_ : _∈P_ {P = ch} ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "(x1 + x2 + x3) * (1 + 2 + 3 * x + y)"
         ExprP
_ = Mul (Add (Var "x1") $ Add (Var "x2") (Var "x3"))
        (Add (Const 1) $ Add (Const 2) $ Add (Mul (Const 3) (Var "x")) (Var "y")) !

{-
_ : _∈P_ {P = ch} ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
         "(x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10) * (y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 + y9 + y10)"
         ExprP
_ = Mul (Add (Var "x1") $
         Add (Var "x2") $
         Add (Var "x3") $
         Add (Var "x4") $
         Add (Var "x5") $
         Add (Var "x6") $
         Add (Var "x7") $
         Add (Var "x8") $
         Add (Var "x9")
             (Var "x10"))
        (Add (Var "y1") $
         Add (Var "y2") $
         Add (Var "y3") $
         Add (Var "y4") $
         Add (Var "y5") $
         Add (Var "y6") $
         Add (Var "y7") $
         Add (Var "y8") $
         Add (Var "y9")
             (Var "y10")) !
-}
