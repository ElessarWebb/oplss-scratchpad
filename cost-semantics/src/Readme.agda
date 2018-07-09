module Readme where

open import Data.Nat
open import Data.Fin using (Fin)
open import Data.Product
open import Data.Vec

data Expr (n : ℕ) : Set where
  var  : Fin n → Expr n
  unit : Expr n
  fun  : Expr (suc n) → Expr n
  app  : (f e : Expr n) → Expr n

data Val (n : ℕ) : Set where
  unit : Val n
  fun  : Expr (suc n) → Val n

⟦_⟧ : ∀ {n} → Val n → Expr n
⟦ unit ⟧ = unit
⟦ fun e ⟧ = fun e

Work Span : Set
Work = ℕ
Span = ℕ

Model : ℕ → Set
Model n = (Val n × Work × Span)

open import Data.Fin.Substitution

module App {ℓ}{T : ℕ → Set ℓ} (l : Lift T Expr) where
  open Lift l hiding (var)

  infix 8 _/_
  _/_ : ∀ {v w} → Expr v → Sub T v w → Expr w
  unit    / ρ = unit
  var x   / ρ = lift (lookup x ρ)
  fun e   / ρ = fun (e / ρ ↑)
  app f e / ρ = app (f / ρ) (e / ρ)

  open Application (record { _/_ = _/_ }) using (_/✶_)

module _ where
  tmSubst : TermSubst Expr
  tmSubst = record { var = var; app = App._/_ }

  open TermSubst tmSubst hiding (var; subst; app) public


data _⇓_ : Expr 0 → Model 0 → Set where

  fun : ∀ {e} →
        fun e ⇓ (fun e , 1 , 1)

  app : ∀ {e₁ e₂ e v v' w₁ w₂ w₃ d₁ d₂ d₃} →
        e₁ ⇓ (fun e , w₁ , d₁) →
        e₂ ⇓ (v   , w₂ , d₂) →
        (e / sub ⟦ v ⟧) ⇓ (v' , w₃ , d₃) →
        (app e₁ e₂) ⇓ (v' , 1 + w₁ + w₂ + w₃ , 1 + (d₁ ⊓ d₂) + d₃)
