# Formal Logic & Type Theory Study
Agda Logic & Mathematics Study

このリポジトリは、型理論に基づいたプログラミング言語 Agda を使用して、数学的構造の構築と論理学の諸定理を証明するための学習アーカイブです。

📂 ディレクトリ・ファイル構成と役割

1. 数学的基礎 (Mathematical Foundations)自然数から始まり、代数的な構造を段階的に構築しています。

Natural.agda:
ペアノの公理に基づく自然数 ($\mathbb{N}$) の定義。加算・乗算の再帰的定義と、結合法則・交換法則などの数学的帰納法による証明。
Integer.agda:
自然数を拡張した整数 ($\mathbb{Z}$) の定義。負の数を含む演算と、より複雑なパターンマッチングによる推論の演習。


2. 論理学：浅い埋め込み (Logic: Shallow Embedding)Agdaの型システムを直接命題として利用し、直観主義論理を学びます。

Logic.agda:連言 ($\land$), 選言 ($\lor$), 否定 ($\neg$) などの論理結合子の型定義。自然演繹の推論規則（導入則・除去則）の関数としての実装。交換法則、分配法則、二重否定導入などの基本的な定理の証明。


3. 論理学：深い埋め込み (Logic: Deep Embedding)論理学そのものを「操作対象のデータ」として定義し、Agda自体の制約を超えた論理体系（古典論理など）を構築します。

DeepLogic.agda:
論理式の構文（Formula データ型）の定義。前提リスト（文脈 $\Gamma$）を用いた推論関係 ($\Gamma \vdash A$) の形式化。二重否定除去 ($DNE$) などの規則を追加することによる、古典論理への拡張。


🚀 学習の進捗と目標

Shallow Embedding の習得: 
Agdaの型システム上で直観主義論理の範囲内での証明が完結できる。古典論理の境界線の理解: 排中律やパースの法則など、直観主義論理では証明できない定理を「仮定」を用いて扱う。

メタ論理の構築:
Deep Embedding を用いて、独自の推論規則を持つ論理体系をプログラムとして操作する。

🛠 開発環境
Language: Agda v2.6.3+
Library: Agda Standard Library (stdlib)
Platform: GitHub Codespaces / VS Code (agda-mode)