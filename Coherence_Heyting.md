---
title: "[Final Coq Project] Coherence of Heyting's arithmetic"
date: 2018-04-10
documentclass: article
tags:
  - DM
  - assignment
  - Coq
  - Heyting
  - arithmetic
  - logic
  - project
  - proof-assistant
  - Letouzey
abstract: 'Proofs assistants Coq project'
---

# Coherence of Heyting's arithmetic in Coq

### Alice Rixte, Farzad JafarRahmani, and Younesse Kaddar (**Teacher**: Pierre Letouzey)

The aim of this project is to prove the coherence of Heyting first order arithmetic (denoted by $HA_1$). Recall that Heyting first order arithmetic is the first order intuitionistic logic theory comprised of Peano's language and axioms.

# 1. Advice and useful notions

## 1.1. Arithmetic

### Decidability

Recall that a proposition $P$ is said to be *decidable* if and only if (iff) $P ∨ ¬ P$ is provable. In Coq, this amounts to prove the existence of an algorithm that outputs a boolean indicating whether the proposition is true of false.

Of course, $P ∨ ¬ P$ can expressed in Coq as

```coq
P \/ ~P
```

(of type `or`, itself of type `Prop`), but there also exists the notation

```coq
{P} + {~P}
```

(of type `sumbool`, itself of type `Type`).

All the elementary comparison arithmetic operators are decidable. As it happens, we will especially use the following elements of the Coq Standard Library:

```coq
le_lt_dec : forall n m : nat, {n <= m} + {m < n}
nat_compare : nat -> nat -> comparison
nat_compare_spec : forall x y, CompSpec eq lt x y (nat_compare x y)
```

The type of `le_lt_dec` enables us to directly use it to construct a term with the `if ... then ... else` statement. In a goal where there is a subterm of the form

```coq
if le_lt_dec x y then ... else ...
```
