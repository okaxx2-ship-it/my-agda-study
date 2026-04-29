module Integer where

open import Logic
-- 自然数の演算子をリネームしてインポート
open import Natural renaming 
  ( _+_ to _+N_
  ; _-_ to _-N_
  ; _*_ to _*N_
  ; _/_ to _/N_
  ; _%_ to _%N_
  )

data ℤ : Set where
  pos  : ℕ → ℤ  
  neg  : ℕ → ℤ  

-- 中略 (diff, -_ , pos-inj-≠ の定義) --
--diff
-- 1. まず「符号反転」を定義（_+_ や _-_ で使うため）
-_ : ℤ → ℤ
- pos zero    = pos zero
- pos (suc n) = neg n
- neg n       = pos (suc n)

-- 2. 次に「差」を計算する関数を定義（_+_ で使うため）
diff : ℕ → ℕ → ℤ
diff zero    n       = neg n       
diff (suc m) zero    = pos (suc m) 
diff (suc m) (suc n) = diff m n

--pos-inj-≠
pos-inj-≠ : {m n : ℕ} → pos m ≢ pos n → m ≢ n
pos-inj-≠ {m} {.m} p refl = p refl


-- 1. 足し算・引き算・掛け算 (シンプル版)
infixl 6 _+_ _-_
infixl 7 _*_ _/_ _%_

_+_ : ℤ → ℤ → ℤ
pos m + pos n = pos (m +N n)
neg m + neg n = neg (suc (m +N n))
pos m + neg n = diff m (suc n)
neg m + pos n = diff n (suc m)

_-_ : ℤ → ℤ → ℤ
x - y = x + (- y)

_*_ : ℤ → ℤ → ℤ
pos m * pos n = pos (m *N n)
neg m * neg n = pos (suc m *N suc n)
pos m * neg n = - (pos (m *N suc n))
neg m * pos n = - (pos (suc m *N n))

-- 2. 割り算 _/_
_/_ : (x y : ℤ) → {notZero : y ≢ pos zero} → ℤ
(_/_) (pos m) (pos n) {nz} = pos ((_/N_) (m) (n) {pos-inj-≠ nz})
(_/_) (neg m) (neg n) {nz} = pos ((_/N_) (suc m) (suc n) {λ ()})
(_/_) (pos m) (neg n) {nz} = - (pos ((_/N_) (m) (suc n) {λ ()}))
(_/_) (neg m) (pos n) {nz} = - (pos ((_/N_) (suc m) (n) {pos-inj-≠ nz}))

-- 3. 余り _%_
_%_ : (x y : ℤ) → {notZero : y ≢ pos zero} → ℤ
(_%_) (pos m) (pos n) {nz} = pos ((_%N_) (m) (n) {pos-inj-≠ nz})
(_%_) (neg m) (neg n) {nz} = - (pos ((_%N_) (suc m) (suc n) {λ ()}))
(_%_) (pos m) (neg n) {nz} = pos ((_%N_) (m) (suc n) {λ ()})
(_%_) (neg m) (pos n) {nz} = - (pos ((_%N_) (suc m) (n) {pos-inj-≠ nz}))

-- 整数用：neg n (つまり -1, -2, ...) で割る
infixl 7 _/neg_
_/neg_ : ℤ → ℕ → ℤ
x /neg n = (_/_) (x) (neg n) {λ ()}

-- 整数用：pos (suc n) (つまり 1, 2, ...) で割る
infixl 7 _/pos_
_/pos_ : ℤ → ℕ → ℤ
x /pos n = (_/_) (x) (pos (suc n)) {(λ ())}