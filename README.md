# Formal Logic & Type Theory Laboratory

**An Experimental Playground for Formal Logic and Type Theory — Agda Edition**

## Overview

This repository is a personal learning laboratory for exploring concepts from formal logic, mathematical logic, and type theory through Agda.

The goal is not merely to understand abstract concepts through lectures and textbooks, but to express them as formal definitions, experiment with their structures, and examine their properties through type checking.

This is neither a professional software development project nor an academic research project. It is simply a record of independent learning, experimentation, and intellectual curiosity.

## Areas of Exploration

The main topics of interest include:

- **Inductive Definitions** — Defining natural number-like structures, terms, logical formulas, and other syntactic objects.
- **Formal Languages** — Exploring syntax and semantics, object languages, and metalanguages.
- **Propositions and Proofs** — Understanding propositions as types and proofs as terms.
- **Curry–Howard Correspondence** — Exploring the relationship between logical systems and type systems.
- **Induction and Recursion** — Defining recursive functions and constructing proofs over inductive data types.
- **Dependent Type Theory** — Learning the foundations of dependent types through Agda's type system.

## Current Experiments

### 01. Inductive Definition of Natural Number-Like Objects

**File:** `NatLike.agda`

This experiment explores how a structure resembling the natural numbers can be defined inductively using a zero constructor and a successor constructor.

```agda
data NatLike : Set where
  zero : NatLike
  suc  : NatLike → NatLike
```

The definition follows two formation rules:

1. `zero` is an element of `NatLike`.
2. If `n` is an element of `NatLike`, then `suc n` is also an element of `NatLike`.

Using these constructors, the examples `one`, `two`, and `three` are also defined.

The purpose of this experiment is to understand how inductive definitions work and how constructors determine the structure of a data type.

## Type Checking

GitHub Actions is configured to automatically type-check Agda source files.

The workflow is intended to check definitions whenever changes are pushed to the repository, helping maintain consistency as the experiments evolve.

## Related Repositories

The same concepts are also explored using other proof assistants:

- [Lean 4 — lean-experiments](https://github.com/okaxx2-ship-it/lean-experiments)
- [Coq / Rocq — coq-experiments](https://github.com/okaxx2-ship-it/coq-experiments)

By expressing similar definitions and proofs in different systems, I hope to gain a deeper understanding of their similarities, differences, and underlying logical foundations.

## A Personal Note

I am neither an engineer nor a researcher, just someone fascinated by logic, formal systems, and the foundations of mathematics.

This repository is a place to learn by experimenting, making mistakes, asking questions, and gradually building a better understanding.

No grand claims, no particular destination — just curiosity and the joy of understanding.

---

*This repository is a personal learning record. Some experiments may be incomplete, exploratory, or subject to revision.*
