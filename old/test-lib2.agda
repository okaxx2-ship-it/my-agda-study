module test-lib2 where  -- ファイル名と同じ名前にする

-- ここから下にコードを書く
-- 自然数の定義
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ  -- 0の次(successor)という意味

-- 1の定義
one : ℕ
one = suc zero

-- 「イコール」という型の定義
data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x  -- 「同じものは同じである」という唯一の証明

one-is-one : one ≡ one
one-is-one = refl
-- リストの定義
data List (A : Set) : Set where
  []  : List A
  _::_ : A → List A → List A  -- 要素とリストをつなぐ

infixr 5 _::_

-- 足し算の定義
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

-- 合計を出す関数
--sum : List ℕ → ℕ
--sum [] = zero
--sum (x :: xs) = x + sum xs

-- 実際にリストを作ってみる (1 :: 0 :: [])
example-list : List ℕ
example-list = one :: zero :: []

-- 「1 ≡ 1」という型の値（証明）をAgdaに探させる
-- proof : one ≡ one
-- proof = ?

-- 今回新しく試したいことだけを活かす
one-plus-one : ℕ
one-plus-one = suc zero
--testzz
