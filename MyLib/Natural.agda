module Natural where

open import Logic

-- 自然数の定義
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-} 

-- 足し算・引き算
infixl 6 _+_ _-_
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

_-_ : ℕ → ℕ → ℕ
zero  - n     = zero
m     - zero  = m
suc m - suc n = m - n

-- 掛け算
infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

-- 比較 (BoolはLogic.agdaで定義済み)
_<_ : ℕ → ℕ → Bool
_     < zero  = false
zero  < suc _ = true
suc m < suc n = m < n

-- 割り算のヘルパー
div-helper : ℕ → ℕ → ℕ → ℕ
div-helper zero    n k = zero
div-helper (suc m) n k with (suc k) < n
... | true  = div-helper m n (suc k)
... | false = suc (div-helper m n zero)

-- 自然数の割り算 (div から / へ)
infixl 7 _/_
_/_ : (m n : ℕ) → {nz : n ≢ 0} → ℕ
(_/_) m zero    {nz} = ⊥-elim (nz refl)
(_/_) m (suc n) {nz} = div-helper m (suc n) zero

-- 余りのヘルパー
mod-helper : ℕ → ℕ → ℕ → ℕ
mod-helper zero    n k = k
mod-helper (suc m) n k with (suc k) < n
... | true  = mod-helper m n (suc k)
... | false = mod-helper m n zero

-- 自然数の余り (mod から % へ)
infixl 7 _%_
_%_ : (m n : ℕ) → {nz : n ≢ 0} → ℕ
(_%_) m zero    {nz} = ⊥-elim (nz refl)
(_%_) m (suc n) {nz} = mod-helper m (suc n) zero

-- リスト操作 (ListはLogic.agdaで定義済み)
length : {A : Set} → List A → ℕ
length [] = zero
length (x :: xs) = suc (length xs)

sum : List ℕ → ℕ
sum [] = zero
sum (x :: xs) = x + sum xs

-- 自然数用：n + 1 で割る（絶対に 0 じゃないので証明いらず）
infixl 7 _/suc_
_/suc_ : ℕ → ℕ → ℕ
m /suc n = ((_/_) (m) (suc n) {λ ()})