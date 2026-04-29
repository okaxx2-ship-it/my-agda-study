module test-lib where
open import Data.Nat using (ℕ; _+_; zero; suc)
-- 「等しさ」の定義をインポート
open import Relation.Binary.PropositionalEquality
-- 10 + 5 を計算してみる
example : ℕ
example = 10 + 5
-- 名前を _mul_ に変えて、標準ライブラリとぶつからないようにする
_mul_ : ℕ → ℕ → ℕ
zero mul n = zero
suc m mul n = n + (m mul n)
-- 「one-is-one」という名前の証明を作る
-- 型（命題）は「1 ≡ 1」
one-is-one : 1 ≡ 1
one-is-one = refl
-- 「1 + 1 は 2 である」という証明
1+1≡2 : 1 + 1 ≡ 2
1+1≡2 = refl
-- 2 + 3 が 5 であることを証明したい（まだ答えは書かない）
2+3≡5 : 2 + 3 ≡ 5
2+3≡5 = refl
-- どんな n に対しても、n + 0 は n と等しい
n+0≡n : (n : ℕ) → n + 0 ≡ n
n+0≡n zero = refl
n+0≡n (suc n) = cong suc (n+0≡n n)