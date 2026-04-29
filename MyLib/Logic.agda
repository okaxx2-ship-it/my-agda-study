module Logic where

------------------------------------------------------------------------------
-- 1. 基礎（等式と矛盾）
------------------------------------------------------------------------------

-- 等号（Equality）
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}  

-- 矛盾（Absurdity / False）
-- 最小論理から直観主義論理への架け橋
data ⊥ : Set where

-- 否定（Negation）
¬_ : Set → Set
¬ A = A → ⊥

-- 不等号（Inequality）
infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

-- 爆発律（Ex Falso Quodlibet）
-- 矛盾からは何でも導ける
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

------------------------------------------------------------------------------
-- 2. 命題論理の結合子（Shallow Embedding）
------------------------------------------------------------------------------

-- 真（Truth）: 常に証明（tt）が存在する
record ⊤ : Set where
  constructor tt

-- 連言（Conjunction / And）: AとBの両方の証明のペア
record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    proj1 : A
    proj2 : B

open _∧_ public
infixr 3 _∧_

-- 選言（Disjunction / Or）: AまたはBの証明のどちらか
data _∨_ (A B : Set) : Set where
  inj1 : A → A ∨ B
  inj2 : B → A ∨ B

open _∨_ public
infixr 2 _∨_

-- ※ 含意（Implication）は Agda の (A → B) をそのまま利用する

------------------------------------------------------------------------------
-- 3. 述語論理（量化）
------------------------------------------------------------------------------

-- ※ 全称量化（Universal）は Agda の依存関数型 ((x : A) → P x) を利用する

-- 存在量化（Existential）: ある値とその性質の証明のペア
record ∃ {A : Set} (P : A → Set) : Set where
  constructor _,,_
  field
    witness : A
    proof   : P witness

------------------------------------------------------------------------------
-- 4. 基本データ型
------------------------------------------------------------------------------

-- 真偽値
data Bool : Set where
  true  : Bool
  false : Bool

-- リスト
infixr 5 _::_ 
data List (A : Set) : Set where
  []  : List A
  _::_ : A → List A → List A
{-# BUILTIN LIST List #-}

------------------------------------------------------------------------------
-- 5. 基本定理 (Shallow Embedding)
------------------------------------------------------------------------------

-- 交換法則: A ∧ B → B ∧ A
∧-comm : {A B : Set} → A ∧ B → B ∧ A
∧-comm (a , b) = (b , a)

-- 分配法則: A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)
distrib : {A B C : Set} → A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)
distrib (a , inj1 b) = inj1 (a , b)
distrib (a , inj2 c) = inj2 (a , c)

-- 二重否定の導入: A → ¬ ¬ A
dn-intro : {A : Set} → A → ¬ ¬ A
dn-intro a f = f a

-- 選言の交換法則: A ∨ B → B ∨ A
∨-comm : {A B : Set} → A ∨ B → B ∨ A
∨-comm (inj1 a) = inj2 a
∨-comm (inj2 b) = inj1 b

-- 三重否定の除去 (Triple Negation Elimination)
-- 直観主義論理で証明可能！
¬¬¬→¬ : {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬→¬ nnnA a = nnnA (dn-intro a)
------------------------------------------------------------------------------
-- 6. 自然演繹の推論規則 (Inference Rules)
------------------------------------------------------------------------------

-- 連言 ∧ (Conjunction)
∧-intro : {A B : Set} → A → B → A ∧ B
∧-intro a b = (a , b)

∧-elim1 : {A B : Set} → A ∧ B → A
∧-elim1 p = proj1 p

∧-elim2 : {A B : Set} → A ∧ B → B
∧-elim2 p = proj2 p

-- 選言 ∨ (Disjunction)
∨-intro1 : {A B : Set} → A → A ∨ B
∨-intro1 a = inj1 a

∨-intro2 : {A B : Set} → B → A ∨ B
∨-intro2 b = inj2 b

-- ∨-除去則は「ケース分析」に対応します
∨-elim : {A B C : Set} → A ∨ B → (A → C) → (B → C) → C
∨-elim (inj1 a) f g = f a
∨-elim (inj2 b) f g = g b

-- 否定 ¬ と 矛盾 ⊥ (Negation and Absurdity)
¬-intro : {A : Set} → (A → ⊥) → ¬ A
¬-intro f = f

¬-elim : {A : Set} → A → ¬ A → ⊥
¬-elim a f = f a

-- ⊥-除去則 (爆発律)
absurd : {A : Set} → ⊥ → A
absurd ()

-- 真 ⊤ (Truth)
⊤-intro : ⊤
⊤-intro = tt

-- 存在量化 ∃ (Existential Quantification)
∃-intro : {A : Set} {P : A → Set} → (x : A) → P x → ∃ P
∃-intro x p = x ,, p

∃-elim : {A : Set} {P : A → Set} {C : Set} → ∃ P → ((x : A) → P x → C) → C
∃-elim (x ,, p) f = f x p
