# Formal Logic & Type Theory Study

このリポジトリは、型理論に基づいたプログラミング言語 Agda を使用して、算数と論理学の定義と証明の練習をするための学習アーカイブです。

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

Shallow Embedding の習得: 

Agdaの型システム上で直観主義論理の範囲内での証明が完結できる。古典論理の境界線の理解: 排中律やパースの法則など、直観主義論理では証明できない定理を「仮定」を用いて扱う。

メタ論理の構築:

Deep Embedding を用いて、独自の推論規則を持つ論理体系をプログラムとして操作する。

🛠 開発環境

Language: Agda v2.6.3+

Library: Agda Standard Library (stdlib)

Platform: GitHub Codespaces / VS Code (agda-mode)