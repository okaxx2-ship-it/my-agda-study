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


🛠 開発環境

Language: Agda v2.6.3+

Library: Agda Standard Library (stdlib)

Platform: GitHub Codespaces / VS Code (agda-mode)