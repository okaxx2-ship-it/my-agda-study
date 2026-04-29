module calc2 where

-- natural numbers
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-} 

-- integer
data ℤ : Set where
  pos  : ℕ → ℤ  -- 0, +1, +2, ... (pos 0 は 0)
  neg  : ℕ → ℤ  -- -1, -2, -3, ... (neg 0 は -1 と定義するのが一般的)

-- 1. まず Bool 型を定義する
data Bool : Set where
  true  : Bool
  false : Bool

-- equal sign
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}  

-- not equal sign
-- 1. まず「矛盾（空の型）」を定義する
data ⊥ : Set where

-- 2. 「否定（¬）」を定義する（ある命題 A から ⊥ が導かれること）
¬_ : Set → Set
¬ A = A → ⊥

-- 3. 「等しくない（≢）」を、等号（≡）の否定として定義する
infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

-- 4. 矛盾から何でも導ける魔法の関数（後の div で使用）
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- LIST
infixr 5 _::_  -- Right join priority 5
data List (A : Set) : Set where
  []  : List A
  _::_ : A → List A → List A
{-# BUILTIN LIST List #-}

--Sign inversion
-_ : ℤ → ℤ
- pos zero    = pos zero
- pos (suc n) = neg n
- neg n       = pos (suc n)

--Determining the difference between natural numbers
diff : ℕ → ℕ → ℤ
diff zero    n       = neg n       -- 0 - n = -n (neg 0 は -1 と解釈)
diff (suc m) zero    = pos (suc m) -- (m+1) - 0 = +(m+1)
diff (suc m) (suc n) = diff m n    -- 両方から1を引いても差は変わらない

--addition
infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

--Integer addition
infixl 6 _+ℤ_
_+ℤ_ : ℤ → ℤ → ℤ
pos m +ℤ pos n = pos (m + n)               -- (正) + (正)
neg m +ℤ neg n = neg (suc (m + n))         -- (負) + (負)
pos m +ℤ neg n = diff m (suc n)            -- (正) + (負)
neg m +ℤ pos n = diff n (suc m)            -- (負) + (正)

--subtraction
infixl 6 _-_

_-_ : ℕ → ℕ → ℕ
zero  - n     = zero
m     - zero  = m
suc m - suc n = m - n

--Integer subtraction
infixl 6 _-ℤ_
_-ℤ_ : ℤ → ℤ → ℤ
x -ℤ y = x +ℤ (- y)

--multiplication
infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

--Integer multiplication
infixl 7 _*ℤ_
_*ℤ_ : ℤ → ℤ → ℤ
pos m *ℤ pos n = pos (m * n)              -- (正) × (正) ＝ (正)
neg m *ℤ neg n = pos (suc m * suc n)      -- (負) × (負) ＝ (正)
pos m *ℤ neg n = - (pos (m * suc n))      -- (正) × (負) ＝ (負)
neg m *ℤ pos n = - (pos (suc m * n))      -- (負) × (正) ＝ (負)

--division
-- 比較用の補助関数
_<_ : ℕ → ℕ → Bool
_       < zero  = false
zero    < suc _ = true
suc m < suc n = m < n

-- 割り算の本体（引き算の回数をカウントする）
-- m: 残りの数, n: 割る数, k: 現在のカウント（余り用）
div-helper : ℕ → ℕ → ℕ → ℕ
div-helper zero    n k = zero
div-helper (suc m) n k with (suc k) < n
... | true  = div-helper m n (suc k)
... | false = suc (div-helper m n zero)

-- 自然数の割り算（0除算は型レベルで防ぐ設定）
-- 修正前：コンストラクタ zero の直後に引数があるように見えている
-- m div zero {nz} = ...
-- 修正後：引数をそれぞれ独立させる
_div_ : (m n : ℕ) → {nz : n ≢ 0} → ℕ
(_div_) m zero    {nz} = ⊥-elim (nz refl)
(_div_) m (suc n) {nz} = div-helper m (suc n) zero

-- Remainder of a natural number
mod-helper : ℕ → ℕ → ℕ → ℕ
mod-helper zero    n k = k
mod-helper (suc m) n k with (suc k) < n
... | true  = mod-helper m n (suc k)
... | false = mod-helper m n zero

_mod_ : (m n : ℕ) → {nz : n ≢ 0} → ℕ
(_mod_) m zero    {nz} = ⊥-elim (nz refl)
(_mod_) m (suc n) {nz} = mod-helper m (suc n) zero

--Integer division

-- 「pos m と pos n が違うなら、m と n も違う」ことを証明する
pos-inj-≠ : {m n : ℕ} → pos m ≢ pos n → m ≢ n
pos-inj-≠ {m} {.m} p refl = p refl

infixl 7 _divℤ_
_divℤ_ : (x y : ℤ) → {notZero : y ≢ pos zero} → ℤ
-- (正) ÷ (正)
(_divℤ_) (pos m) (pos n) {nz} = pos ( (_div_) m n {pos-inj-≠ nz})
-- (負) ÷ (負) : 両方負なら結果は正。neg n は -(n+1) なので suc を補う
(_divℤ_) (neg m) (neg n) {nz} = pos ((_div_) (suc m) (suc n) {λ ()})
-- (正) ÷ (負) : 結果は負。符号反転関数『-_』を使用
(_divℤ_) (pos m) (neg n) {nz} = - (pos ((_div_) (m) (suc n) {λ ()} ))
-- (負) ÷ (正) : 結果は負
(_divℤ_) (neg m) (pos n) {nz} = - (pos ((_div_) (suc m) (n){pos-inj-≠ nz}))
-- Remainder of an integer
infixl 7 _modℤ_
_modℤ_ : (x y : ℤ) → {notZero : y ≢ pos zero} → ℤ
-- (正) mod (正)
--pos m modℤ pos n {nz} = pos (m mod n {nz})
(_modℤ_) (pos m) (pos n) {nz} = pos ((_mod_) m n {pos-inj-≠ nz})
-- (負) mod (負) : 絶対値で計算し、結果をマイナスにする（一例）
--neg m modℤ neg n {nz} = - (pos (suc m mod suc n))
(_modℤ_) (neg m) (neg n) {nz} = - (pos ((_mod_) (suc m)  (suc n) {λ ()}))
-- (正) mod (負) : 余りの符号は割られる数(左側)に合わせるのが一般的
(_modℤ_) (pos m) (neg n) {nz} = pos ((_mod_) m (suc n){λ ()})
-- (負) mod (正)
(_modℤ_) (neg m) (pos n) {nz} = - (pos ((_mod_) (suc m) (n) {pos-inj-≠ nz}))

---Function or proof area-----------------------------------------------

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
