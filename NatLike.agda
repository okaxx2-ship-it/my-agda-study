module NatLike where

-- 自然数もどきの帰納的定義
data NatLike : Set where
  zero : NatLike
  suc  : NatLike → NatLike

-- 自然数もどきの具体例
one : NatLike
one = suc zero

two : NatLike
two = suc (suc zero)

three : NatLike
three = suc (suc (suc zero))
