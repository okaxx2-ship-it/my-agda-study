# Formal Logic & Type Theory Study

このリポジトリはAgdaを使用してデータ型や関数の定義とそれら証明の練習をするための場所として作りました

📂 ディレクトリ・ファイル構成と役割

Natural.agda:

自然数、四則演算、リスト、等号

Integer.agda:

整数、負の数を含む四則演算

Logic.agda:

浅い埋め込み (Logic: Shallow Embedding)

直観主義論理と最小論理

∧連言, ∨選言 ,¬ 否定 などの論理結合子

論理結合子の導入規則と除去規則

交換法則、分配法則、二重否定導入

DeepLogic.agda:

深い埋め込み (Logic: Deep Embedding)

古典論理など

論理式の構文（Formula データ型）

前提リストを用いた推論関係の形式化（推件計算）

二重否定除去などの規則を追加することによる、古典論理への拡張


🚀 学習の進捗と目標
Geminiに手伝ってもらいながら大風呂敷を拡げるようにいろいろなデータ型や関数を定義してここに登録したけど自分自身これらの内容に全然ついていけてないので簡単な定義から少しずつ理解していく。Geminiに手伝ってもらいながら。



260519
とりあえず Bool型 Nat型 List型 Array型 _+_関数 _==_関数の定義内容を日本語に置き換えた。Geminiに手伝ってもらいながら。

【Bool型】
data Bool : Set where
 true : Bool
 false : Bool

これから Bool という名前のデータ型（data）を定義します
Bool 型自体の型は Set です（Bool は「型」という世界の住人です）
Bool 型の中身は次の通り（where）です
true と false という名前の構成子（要素）を持ちます
true は Bool 型の値（データ）です
false は Bool 型の値（データ）です

【Nat型】
data Nat : Set where
 zero : Nat
 suc : Nat → Nat

これから Nat という名前のデータ型（data）を定義します
Nat 型自体の型は Set です（Nat は「型」という世界の住人です）
Nat 型の中身は次の通り（where）です
zero と suc という名前の構成子（要素）を持ちます
zero は Nat 型の値（データ）です
suc は Nat 型の値（データ）を入力するとNat 型の値（データ）を出力する構成子です

【List 型】
data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

これから List という名前のデータ型（data）を定義します
この List は、Set 型の住人である任意の型 A を1つ入力として受け取ります
型 A を受け取って出来上がる List A 型自体の型は Set です（List A は「型」という世界の住人です）
List A 型の中身は次の通り（where）です
[] と _::_ という名前の構成子（要素）を持ちます
[] は List A 型の値（データ）です
_::_ は :: の左側に A 型の値（データ）を入力して :: の右側に List A 型の値（データ）を入力すると List A 型の値（データ）を出力する構成子です

🛠 開発環境

Language: Agda v2.6.3+

Library: Agda Standard Library (stdlib)

Platform: GitHub Codespaces / VS Code (agda-mode)