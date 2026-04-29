module DeepLogic where

open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; []; _++_)
open import Data.List.Membership.Propositional using (_∈_)

------------------------------------------------------------------------------
-- 1. 論理式の構文定義 (Syntax)
------------------------------------------------------------------------------

data Formula : Set where
  Var : ℕ → Formula           -- 命題変数 (P₀, P₁, ...)
  Bot : Formula               -- 矛盾 ⊥
  _⇒_ : Formula → Formula → Formula   -- 含意 →
  _∧_ : Formula → Formula → Formula   -- 連言 ∧
  _∨_ : Formula → Formula → Formula   -- 選言 ∨

infixr 4 _⇒_
infixr 3 _∧_
infixr 2 _∨_

-- 否定の定義 (¬A は A ⇒ ⊥ の略記)
neg : Formula → Formula
neg A = A ⇒ Bot

------------------------------------------------------------------------------
-- 2. 推論規則の定義 (Natural Deduction: Γ ⊢ A)
------------------------------------------------------------------------------

data _⊢_ : List Formula → Formula → Set where

  -- (1) 仮定 (Assumption)
  -- 文脈 Γ の中に A が含まれているなら、Γ から A を導いてよい
  Assume : {Γ : List Formula} {A : Formula} 
         → A ∈ Γ 
         → Γ ⊢ A

  -- (2) 含意 (Implication)
  ⇒-I : {Γ : List Formula} {A B : Formula} 
       → (A ∷ Γ) ⊢ B 
       → Γ ⊢ (A ⇒ B)

  ⇒-E : {Γ : List Formula} {A B : Formula} 
       → Γ ⊢ (A ⇒ B) 
       → Γ ⊢ A 
       → Γ ⊢ B

  -- (3) 連言 (Conjunction)
  ∧-I : {Γ : List Formula} {A B : Formula} 
       → Γ ⊢ A 
       → Γ ⊢ B 
       → Γ ⊢ (A ∧ B)

  ∧-E1 : {Γ : List Formula} {A B : Formula} 
        → Γ ⊢ (A ∧ B) 
        → Γ ⊢ A

  ∧-E2 : {Γ : List Formula} {A B : Formula} 
        → Γ ⊢ (A ∧ B) 
        → Γ ⊢ B

  -- (4) 選言 (Disjunction)
  ∨-I1 : {Γ : List Formula} {A B : Formula} 
        → Γ ⊢ A 
        → Γ ⊢ (A ∨ B)

  ∨-I2 : {Γ : List Formula} {A B : Formula} 
        → Γ ⊢ B 
        → Γ ⊢ (A ∨ B)

  ∨-E : {Γ : List Formula} {A B C : Formula} 
       → Γ ⊢ (A ∨ B) 
       → (A ∷ Γ) ⊢ C 
       → (B ∷ Γ) ⊢ C 
       → Γ ⊢ C

  -- (5) 矛盾と爆発律 (Absurdity)
  ⊥-E : {Γ : List Formula} {A : Formula} 
       → Γ ⊢ Bot 
       → Γ ⊢ A

  ----------------------------------------------------------------------------
  -- (6) 古典論理のための拡張ルール
  ----------------------------------------------------------------------------
  -- 直観主義論理として扱う場合はここをコメントアウトします。
  -- これを追加することで、排中律や二重否定除去が証明可能になります。

  DNE : {Γ : List Formula} {A : Formula} 
       → Γ ⊢ (neg (neg A)) 
       → Γ ⊢ A