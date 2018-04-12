---
title: "[Final Coq Project] Coherence of Heyting's arithmetic"
date: 2018-04-10
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

The type of `le_lt_dec` enables us to directly use it to construct a term with the `if ... then ... else` statement. For a goal where there is a subterm of the form

```coq
if le_lt_dec x y then ... else ...
```

a case analysis can be done by using

```coq
destruct (le_lt_dec x y)
```

this generates two subgoals: the first one corresponding to the `x <= y` case, and the second one to `y < x`.

The `nat_compare` function is little bit more general: it returns an object of type `comparison`, different in the three possible cases. For a goal where there is a subterm of the form

```coq
match nat_compare x y with ...
```

a case analysis can be done by using the tactic

```coq
destruct (nat_compare_spec x y)
```

which generates three subgoals, corresponding to the three possible cases: `x=y`, `x<y`, and `x>y`

It is also possible to use

```coq
case_eq (nat_compare x y)
```

and then specific lemmas for each case (which can be found with the command `SearchAbout`). A `case nat_compare` can also be useful.

### Axiomatization

Certain fragments of arithmetic can be decidable, and there exist some tactics to solve them. The proofs in this project resort to one of these fragments: *Presburger arithmetic*.

Presburger arithmetic roughly corresponds to Peano first order arithmetic where there is nothing but addition. In Coq, the `omega` tactic solves a significant part thereof. In particular, all the goals involving only additions and comparisons can be directly proved. As a matter of fact, this tactic makes use of the associativity and commutativity of addition, of the transitivity of inequalities, and of existing compatibilities between the addition and inequalities.

## 1.2 Other convenient tactics

For more details, refer to the Coq reference manual.

- In this project, automatic tactics such as `auto` and `intuition` are allowed

- The `f_equal` tactic can help proving equalities of the form `f x ... = f x' ...` by proving equalities between arguments: `x=x'`, and so on...

- The `simpl` tactic simply expands the definitions and compute.

- It can happen that one wishes to convert a subterm into another one which is definitionally equal. This can be done with the `change` tactic.

- The `replace` tactic replaces a subterm by another, provided that both are provably equal.

- The `set` and `pose` tactics give names to subterms (by setting local definitions). They come in handy when it comes to clarifying a goal, or simplifying the names of the arguments of certain tactics.

- Lemmas dealing with logical equivalences are conveniently usable with the `apply` tactic. For instance, if you have a lemma `foe: A <--> B`, then `apply <- foe` or `apply -> foe` applies a direction of the equivalence. It is also possible to use `rewrite`(as well as for the equality) after loading the `Setoid` library.

- There exists an `admit` tactic to admit a subgoal without proving it. For obvious reasons, using this tactic is not recommended, but it can still prove convenient when it comes to focusing on specific parts of a proof. It goes without saying that the final mark with highly depend on the number of `Axiom` (and `Parameter`), `admit` and `Admitted` remaining in the code.

- The `Print Assumption` command identifies all the axioms used in the proof of a proposition.

## 1.3. Methodology

All the expected definitions and lemmas are explicitely asked and mentioned in the questions of this problem statement. It is not necessary to prove everything in order: a lemma can be proven with the purpose of proving another subsequent one. However, the order of the statements has to be respected.

It is of course allowed to introduce new intermediate lemmas other than the ones stated in this problem statement (but at least these stated lemmas have to be proven).

# 2. Syntax

In this section, one defines the *object language* to study, i.e. the notions of *terms*, *formulas*, and *derivation* (and hence theorem) of $HA_1$. These definitions can be exppressed in Coq, which acts as a *meta language* in which the properties of the studied logical system are to be expressed and proven.

## 2.1. Terms and formulas

For the sake of simplicity, we limit ourselves to the Peano language, even though everything that is done here could be more general, as seen in class.

The first order terms involve free variables and bound (by quantifiers) ones. The definition of substitution is nettlesome owing to variable binding: $α$-equivalence has been introduced to get around this problem. However, the definition of substitution relying on $α$-equivalence is tricky to implement in Coq, and unpractical to use. This the reason why we will adopt another representation of the terms, with *De Bruijn* indices.

In this setting, a variable is encoded by a number: the number of quantifiers above it (i.e. its ancestors), in the syntax tree of the formula. Free variables are variables which go "too high" in the tree. The type of terms is:

```coq
Inductive term :=
  | Tvar : nat -> term
  | Tzero : term
  | Tsucc : term -> term
  | Tplus : term -> term -> term
  | Tmult : term -> term -> term.
```

and the type of formulas:

```coq
Inductive formula :=
  | Fequal : term -> term -> formula
  | Ffalse : formula
  | Fand : formula -> formula -> formula
  | For : formula -> formula -> formula
  | Fimplies : formula -> formula -> formula
  | Fexists : formula -> formula
  | Fforall : formula -> formula.
```

Therefore, with this encoding, the formula:

$$∀n \; ∃p \; n = 1 \ast p$$

is represented by:

```coq
Fforall (Fexists (Fequal (Tvar 1) (Tmult (Tsucc Tzero) (Tvar 0))))
```

This representation has the advantage that two $α$-equivalent formulas are syntactically equal. However, the binding phenomenon can still happen, you'd better be careful. Luckily, these precautions are rather systematic and can be ensured with the `tlift` and `flift` functions, as well as a series of provided lemmas. Look closely at these, you will need them later.

## 2.2. Closed expressions

With *De Bruijn* indices, the notion of set of free variables seen in class is replaced by an upper bound for all the variables appearing in the expression. The predicate `cterm n t` means that all the variables of `t` are stricly lower than `n`. Beware though: quantifiers are taken into account. Going through a quantifier increments the upper bound by one. The `cterm` and `cformula` predicates are inductively defined.

_________

### *Questions*

## 1. Prove the following lemmas:

```coq
Lemma cterm_1 : forall n t, cterm n t ->
forall n', n <= n' -> cterm n' t.
Lemma cterm_2 : forall n t, cterm n t ->
forall k, tlift k t n = t.
Lemma cterm_3 : forall n t, cterm n t ->
forall t' j, n <= j -> tsubst j t' t = t.
Lemma cterm_4 : forall n t, cterm (S n) t ->
forall t', cterm 0 t' -> cterm n (tsubst n t' t).
```

The first proof is done by induction on the term and by analysing the constructors of the inductive predicate `cterm` with `inversion`.

```coq
Lemma cterm_1 : forall n t, cterm n t -> forall n', n <= n' -> cterm n' t.
Proof.
  intros; induction t; auto; inversion H; auto.
Qed.
```

## 2. Prove the analogous lemmas for formulas.


_________


## 2.3 Natural deduction

A natural deduction derivation of the judgement $e ⊢ A$ is written in Coq as `ND e A`. The `ND` predicate is defined inductively with the rules of natural deduction, adapted to the use of *De Bruijn* indices.

__________

### *Questions*

## 1. In the language and the derivation rules, we omitted the connectors $⊤$ (`Ftrue`), the negation (`Fnot`), and the equivalence (`Fequiv`). Define them, and prove that the associated introduction and elimination rules are admissible.


## 2. Define an operator `nFforall` which iterates the operator `Fforall`. For instance, the formula `nFforall 2 A` should be tantamount to `Fforall (Fforall A)`. Prove the following lemma:

```coq
Lemma nFforall_1 : forall n x t A,
fsubst x t (nFforall n A) = nFforall n (fsubst (n + x) t A).
```

__________

## 2.4. Notations

For the sake of readability, notations were introduced in the base file to redefine many standard Coq notations, but in a different *scope*. As it happens, already existing notations have classic interpretations (at the *meta* level), but newly introduced interprétations (at the *object* language level) can be used with the notation `(...)%pa`. For example, `A \/ B` represents the *meta* conjunction, and `(A \/ B)%` the *object* one (i.e. the formula `Fand A B`).

## 2.5. Theory

Peano axioms are written in the base file thanks the `Ax` predicate: the proposition `Ax P` means that `P` is a Peano axiom. Pay heed to how `Ax` is defined. This very definition enables us to in Coq the notion of `theorem`:

```coq
Definition Th T := exists axioms,
  (forall A, In A axioms -> Ax A) /\ ND axioms T.
```

_________

### *Questions*

## 1. Prove the following formula in $HA_1$:

$$∀n \quad n ≠ s(n)$$

**NB**: The proof is required to be made at the *object* level: you have to express this formula as a Coq term `A` of type `formula`, and then prove `Th A`


_________


# 3. Semantics

The proof of the coherence of $HA_1$ proposed here relies on constructing a model of Coq type `nat`.

## 3.1.

A valuation of variables is represented by a list `b` of values (which are `nat` here): the $i$-th variable is interpreted by the $i$-th element of the list (denoted by `nth i b 0`). In the base file, the following functions are defined:

```coq
tinterp : list nat -> term -> nat
finterp : list nat -> formula -> Prop
```

These give an interpretation of *object* terms and formulas as Coq integers and propositions.

An object formula (of type `formula`) is said to be valid if its interpretation is provable in Coq.

_________

### *Questions*

## 1. Prove the following lemmas:

```coq
Lemma tinterp_1 : forall t' t b1 b2,
tinterp (b1 ++ b2) (tsubst (length b1) t' t) =
tinterp (b1 ++ (tinterp b2 t') :: b2) t.
Lemma tinterp_2 : forall t j, cterm j t ->
forall b1 b2, j <= length b1 -> j <= length b2 ->
(forall i, i < j -> nth i b1 0 = nth i b2 0) ->
tinterp b1 t = tinterp b2 t.
Lemma tinterp_3 : forall t b0 b1 b2,
tinterp (b0++b2) t =
tinterp (b0++b1++b2) (tlift (length b1) t (length b0)).
```

## 2. Prove the analogous lemmas for formulas.


_________

## 3.2. Correctness of the model

_________

### *Questions*

## 1. Prove that the natural deduction rules are correct with respect to the interpretation of formulas:

```coq
Lemma ND_soundness : forall e A, ND e A ->
    forall b, (forall B, In B e -> finterp b B) -> finterp b A.
```

## 2. Prove that all Peano axioms are valid

```coq
Lemma Ax_soundness : forall A, Ax A -> forall b, finterp b A.
```

## 3. Conclude by showing that `Ffalse` is not a theorem:

```coq
Theorem coherence : ~Th Ffalse.
```
