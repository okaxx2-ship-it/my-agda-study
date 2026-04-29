module calc where
-- 自然数
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- 等式
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- リスト
infixr 5 _::_  -- 右結合 優先度５
data List (A : Set) : Set where
  []  : List A
  _::_ : A → List A → List A

--足し算
infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

--引き算
infixl 6 _-_

_-_ : ℕ → ℕ → ℕ
zero  - n     = zero
m     - zero  = m
suc m - suc n = m - n

--掛け算
infixl 7 _*_

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

--割り算
-- 比較用の補助関数（以下であれば true）
data Bool : Set where
  true false : Bool

_<_ : ℕ → ℕ → Bool
_     < zero  = false
zero  < suc _ = true
suc m < suc n = m < n

-- 割り算本体（m ÷ n）
-- ※ 0での除算はここでは単純に 0 を返すようにしています
div-helper : ℕ → ℕ → ℕ → ℕ
div-helper zero    n k = zero
div-helper (suc m) n k with (suc k) < n
... | true  = div-helper m n (suc k)
... | false = suc (div-helper m n zero)

_/_ : ℕ → ℕ → ℕ
m / zero  = zero  -- 0除算の例外処理
m / suc n = div-helper m (suc n) zero


--------------------------------------------------

example-list : List ℕ
example-list = suc zero :: suc (suc zero) :: suc (suc (suc zero)) :: []

length : List ℕ → ℕ
length [] = zero
length (x :: xs) = suc (length xs)

sum : List ℕ → ℕ
sum [] = zero
sum (x :: xs) = x + sum xs

test-length : length (suc zero :: suc (suc zero) :: suc (suc (suc zero)) :: []) ≡ suc (suc (suc zero))
test-length = refl