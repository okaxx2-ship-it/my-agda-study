module hello where

-- 自然数の定義（ライブラリを使わず自分で定義する）
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- 「1」を定義
one : ℕ
one = suc zero
-- 1 + 1 の代わりに「2」を定義してみる例
two : ℕ
two = suc(suc(zero))
-- 足し算のルール
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)