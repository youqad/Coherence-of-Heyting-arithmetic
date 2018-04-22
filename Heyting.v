(**************************************************************************)
(*              Coherence of first-order Heyting arithmetic               *)
(*                                                                        *)
(*                         © 2011 Stéphane Glondu                         *)
(*                         © 2013 Pierre Letouzey                         *)
(*   modified by Alice Rixte, Farzad JafarRahmani, and Younesse Kaddar    *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*   it under the terms of the CeCILL free software license, version 2.   *)
(**************************************************************************)

Require Import List Arith Omega.

(* Tactics *)

(* First, tell the "auto" tactic to use the "omega" solver. *)

Hint Extern 8 (_ = _ :> nat) => omega.
Hint Extern 8 (_ <= _) => omega.
Hint Extern 8 (_ < _) => omega.
Hint Extern 8 (_ <> _ :> nat) => omega.
Hint Extern 8 (~ (_ <= _)) => omega.
Hint Extern 8 (~ (_ < _)) => omega.
Hint Extern 12 => exfalso; omega.

(* Destructing the <=? and ?= (in)equality tests, useful when proving facts
   about "if ... then ... else" code. *)

Ltac break := match goal with
 | |- context [ ?x <=? ?y ] => destruct (Nat.leb_spec x y)
 | |- context [ ?x ?= ?y ] => destruct (Nat.compare_spec x y)
end.


(* Terms : first-order terms over the Peano signature 0 S + *.
   The variable are represented as De Bruijn indices. *)

Inductive term :=
  | Tvar : nat -> term
  | Tzero : term
  | Tsucc : term -> term
  | Tplus : term -> term -> term
  | Tmult : term -> term -> term.

Hint Extern 10 (Tvar _ = Tvar _) => f_equal.

(* Term lifting: add n to all variables of t which are >= k *)

Fixpoint tlift n t k :=
  match t with
    | Tvar i => Tvar (if k <=? i then n+i else i)
    | Tzero => Tzero
    | Tsucc u => Tsucc (tlift n u k)
    | Tplus u v => Tplus (tlift n u k) (tlift n v k)
    | Tmult u v => Tmult (tlift n u k) (tlift n v k)
  end.

Lemma tlift_1 : forall t n n' k k', k <= k' -> k' <= k + n ->
  tlift n' (tlift n t k) k' = tlift (n' + n) t k.
Proof.
  induction t; intros; simpl; f_equal; repeat break; auto.
Qed.

Lemma tlift_2 : forall t n n' k k', k' <= k ->
  tlift n' (tlift n t k) k' = tlift n (tlift n' t k') (n' + k).
Proof.
  induction t; intros; simpl; f_equal; repeat break; auto.
Qed.

Hint Resolve tlift_1 tlift_2.

(* Term substitution: replace variable x by (tlift x t' 0) in t *)

Fixpoint tsubst x t' t :=
  match t with
    | Tvar i =>
      match x ?= i with
        | Eq => tlift x t' 0
        | Lt => Tvar (pred i)
        | Gt => Tvar i
      end
    | Tzero => Tzero
    | Tsucc u => Tsucc (tsubst x t' u)
    | Tplus u v => Tplus (tsubst x t' u) (tsubst x t' v)
    | Tmult u v => Tmult (tsubst x t' u) (tsubst x t' v)
  end.

Lemma tsubst_1 : forall t x t' n k, k <= x -> x <= k + n ->
  tsubst x t' (tlift (S n) t k) = tlift n t k.
Proof.
  induction t; intros; simpl; f_equal; auto.
  repeat (break; simpl; auto).
Qed.

Lemma tsubst_2 : forall t x t' n k, k <= x ->
  tlift n (tsubst x t' t) k = tsubst (n + x) t' (tlift n t k).
Proof.
  induction t; intros; simpl; f_equal; auto.
  repeat (break; simpl; auto).
Qed.

Hint Resolve tsubst_1 tsubst_2.

Lemma tsubst_3 : forall t x t' n k,
  tlift n (tsubst x t' t) (x + k) =
  tsubst x (tlift n t' k) (tlift n t (x + S k)).
Proof.
  induction t; intros; simpl; f_equal; auto.
  repeat (break; simpl; auto).
  symmetry. auto.
Qed.

Lemma tsubst_4 : forall t x t' y u',
  tsubst (x + y) u' (tsubst x t' t) =
  tsubst x (tsubst y u' t') (tsubst (x + S y) u' t).
Proof.
  induction t; intros; simpl; try (f_equal; auto; fail).
  repeat (break; simpl; auto);
   symmetry; rewrite <- ?plus_n_Sm; auto.
Qed.

(* Terms where all variables are < n *)

Inductive cterm n : term -> Prop :=
  | cterm_var : forall i, i < n -> cterm n (Tvar i)
  | cterm_zero : cterm n (Tzero)
  | cterm_succ : forall u, cterm n u -> cterm n (Tsucc u)
  | cterm_plus : forall u v, cterm n u -> cterm n v -> cterm n (Tplus u v)
  | cterm_mult : forall u v, cterm n u -> cterm n v -> cterm n (Tmult u v).

Hint Constructors cterm.

Lemma cterm_1 : forall n t, cterm n t -> forall n', n <= n' -> cterm n' t.
Proof.
  intros; induction t; auto; inversion H; auto.
Qed.


Lemma cterm_2 : forall n t, cterm n t -> forall k, tlift k t n = t.
Proof.
  induction t; intros; inversion H; unfold tlift; repeat break; f_equal; auto.
Qed.


Lemma cterm_3 : forall n t, cterm n t -> forall t' j, n <= j -> tsubst j t' t = t.
Proof.
  intros.
  assert (H' := H).
  apply cterm_2 with (k := j) in H.
  apply cterm_2 with (k := S j) in H'.
  rewrite <- H' at 1; rewrite <- H at 2.
  apply (@tsubst_1 _ j _ j n); auto.
Qed.


Lemma cterm_4 : forall n t, cterm (S n) t ->
  forall t', cterm 0 t' -> cterm n (tsubst n t' t).
Proof.
  induction t; induction t'; induction n; intros; 
  inversion H; inversion H0; repeat (simpl; intuition);
  inversion H2; repeat (simpl; intuition);
  destruct n0; repeat (break; simpl; intuition);
  repeat (intuition; simpl); 
  repeat (rewrite (@cterm_2 0 _); apply (@cterm_1 0 _)); repeat auto.
Qed.

(* Formulas of Heyting Arithmetic. *)

Inductive formula :=
  | Fequal : term -> term -> formula
  | Ffalse : formula
  | Fand : formula -> formula -> formula
  | For : formula -> formula -> formula
  | Fimplies : formula -> formula -> formula
  | Fexists : formula -> formula
  | Fforall : formula -> formula.

Delimit Scope pa_scope with pa.
Bind Scope pa_scope with term.
Bind Scope pa_scope with formula.
Arguments Tsucc _%pa.
Arguments Tplus _%pa _%pa.
Arguments Tmult _%pa _%pa.
Arguments Fequal _%pa _%pa.
Arguments Fand _%pa _%pa.
Arguments For _%pa _%pa.
Arguments Fimplies _%pa _%pa.
Arguments Fexists _%pa.
Arguments Fforall _%pa.

(* Formula lifting: add n to all variables of t which are >= k *)

Fixpoint flift n A k :=
  match A with
    | Fequal u v => Fequal (tlift n u k) (tlift n v k)
    | Ffalse => Ffalse
    | Fand B C => Fand (flift n B k) (flift n C k)
    | For B C => For (flift n B k) (flift n C k)
    | Fimplies B C => Fimplies (flift n B k) (flift n C k)
    | Fexists B => Fexists (flift n B (S k))
    | Fforall B => Fforall (flift n B (S k))
  end.

Lemma flift_1 : forall A n n' k k', k <= k' -> k' <= k + n ->
  flift n' (flift n A k) k' = flift (n' + n) A k.
Proof.
  induction A; intros; simpl; f_equal; auto.
Qed.

Lemma flift_2 : forall A n n' k k', k' <= k ->
  flift n' (flift n A k) k' = flift n (flift n' A k') (n' + k).
Proof.
  induction A; intros; simpl; f_equal; rewrite ?plus_n_Sm; auto.
Qed.

(* Formula substitution: replace variable x by (tlift x t' 0) in A *)

Fixpoint fsubst x t' A :=
  match A with
    | Fequal u v => Fequal (tsubst x t' u) (tsubst x t' v)
    | Ffalse => Ffalse
    | Fand B C => Fand (fsubst x t' B) (fsubst x t' C)
    | For B C => For (fsubst x t' B) (fsubst x t' C)
    | Fimplies B C => Fimplies (fsubst x t' B) (fsubst x t' C)
    | Fexists B => Fexists (fsubst (S x) t' B)
    | Fforall B => Fforall (fsubst (S x) t' B)
  end.

Lemma fsubst_1 : forall A x t' n k, k <= x -> x <= k + n ->
  fsubst x t' (flift (S n) A k) = flift n A k.
Proof.
  induction A; intros; simpl; f_equal; auto.
Qed.

Lemma fsubst_2 : forall A x t' n k, k <= x ->
  flift n (fsubst x t' A) k = fsubst (n + x) t' (flift n A k).
Proof.
  induction A; intros; simpl; f_equal; rewrite ?plus_n_Sm; auto.
Qed.

Lemma fsubst_3 : forall A x t' n k,
  flift n (fsubst x t' A) (x + k) =
  fsubst x (tlift n t' k) (flift n A (x + S k)).
Proof.
  induction A; intros; simpl; f_equal; auto using tsubst_3;
  apply (IHA (S x)).
Qed.

Lemma fsubst_4 : forall A x t' y u',
  fsubst (x + y) u' (fsubst x t' A) =
  fsubst x (tsubst y u' t') (fsubst (x + S y) u' A).
Proof.
  induction A; intros; simpl; f_equal; auto using tsubst_4;
  apply (IHA (S x)).
Qed.

(* Formulas where all variables are < n *)

Inductive cformula n : formula -> Prop :=
  | cformula_equal : forall u v,
    cterm n u -> cterm n v -> cformula n (Fequal u v)
  | cformula_false : cformula n Ffalse
  | cformula_and : forall B C,
    cformula n B -> cformula n C -> cformula n (Fand B C)
  | cformula_or : forall B C,
    cformula n B -> cformula n C -> cformula n (For B C)
  | cformula_implies : forall B C,
    cformula n B -> cformula n C -> cformula n (Fimplies B C)
  | cformula_exists : forall B,
    cformula (S n) B -> cformula n (Fexists B)
  | cformula_forall : forall B,
    cformula (S n) B -> cformula n (Fforall B).

Hint Constructors cformula.

Inductive subterm t: formula -> Prop :=
  | subterm_equal : forall t', subterm t (Fequal t t')
  | subterm_and : forall B C t',
    subterm t B -> subterm t' C -> subterm t (Fand B C)
  | subterm_or : forall B C t',
    subterm t B -> subterm t' C -> subterm t (For B C)
  | subterm_implies : forall B C t',
    subterm t B -> cformula t' C -> subterm t (Fimplies B C)
  | subterm_exists : forall B,
    subterm t B -> subterm t (Fexists B)
  | subterm_forall : forall B,
    subterm t B -> subterm t (Fforall B).

Hint Constructors subterm.


Lemma cformula_1 : forall n A, cformula n A ->
  forall n', n <= n' -> cformula n' A.
Proof.
  intros; generalize dependent n; generalize dependent n';
  induction A; intros; eauto; inversion H; eauto.
  apply cterm_1 with (n':=n') in H3;
  apply cterm_1 with (n':=n') in H4;
  eauto.
Qed.

Lemma cformula_2 : forall n A, cformula n A -> forall k, flift k A n = A.
Proof.
  intros; generalize dependent n; induction A;
  intros; eauto; inversion H; simpl; f_equal;
  try apply cterm_2; eauto.
Qed.

Lemma cformula_3 : forall n A, cformula n A ->
  forall t' j, n <= j -> fsubst j t' A = A.
Proof.
  intros; generalize dependent n; 
  generalize dependent j; induction A;
  intros; eauto; inversion H; simpl; f_equal;
  try apply cterm_3 with (t:=t) (n:=n);
  try apply cterm_3 with (t:=t') (n:=n);
  try apply cterm_3 with (t:=t0) (n:=n);
  eauto.
Qed.

Lemma cformula_4 : forall n A, cformula (S n) A ->
  forall t', cterm 0 t' -> cformula n (fsubst n t' A).
Proof.
  intros; generalize dependent n;
  induction A; intros; eauto; inversion H;
  simpl; 
  try apply cterm_4 with (t':=t') in H3;
  try apply cterm_4 with (t':=t') in H4;
  eauto.
Qed.

(* Notations *)

Reserved Notation "A ==> B" (at level 86, right associativity).
Reserved Notation "# n" (at level 2).

Notation "A /\ B" := (Fand A B) : pa_scope.
Notation "A \/ B" := (For A B) : pa_scope.
Notation "A ==> B" := (Fimplies A B) : pa_scope.
Notation "x = y" := (Fequal x y) : pa_scope.
Notation "x + y" := (Tplus x y) : pa_scope.
Notation "x * y" := (Tmult x y) : pa_scope.
Notation "# n" := (Tvar n) (at level 2) : pa_scope.

Close Scope nat_scope.
Close Scope type_scope.
Close Scope core_scope.
Open Scope pa_scope.
Open Scope core_scope.
Open Scope type_scope.
Open Scope nat_scope.

(* Contexts (or environments), represented as list of formulas. *)

Definition context := list formula.

(* Lifting an context *)

Definition clift n Γ k := map (fun A => flift n A k) Γ.

(* Rules of (intuitionistic) Natural Deduction.

   This predicate is denoted with the symbol ":-", which
   is easier to type than "⊢".
   After this symbol, Coq expect a formula, hence uses the formula
   notations, for instance /\ is Fand instead of Coq own conjunction).
*)

Reserved Notation "Γ :- A" (at level 87, no associativity).

Inductive rule : context -> formula -> Prop :=
  | Rax Γ A : In A Γ -> Γ:-A
  | Rfalse_e Γ : Γ:-Ffalse -> forall A, Γ:-A
  | Rand_i Γ B C : Γ:-B -> Γ:-C -> Γ:-B/\C
  | Rand_e1 Γ B C : Γ:-B/\C -> Γ:-B
  | Rand_e2 Γ B C : Γ:-B/\C -> Γ:-C
  | Ror_i1 Γ B C : Γ:-B -> Γ:-B\/C
  | Ror_i2 Γ B C : Γ:-C -> Γ:-B\/C
  | Ror_e Γ A B C : Γ:-B\/C -> (B::Γ):-A -> (C::Γ):-A -> Γ:-A
  | Rimpl_i Γ B C : (B::Γ):-C -> Γ:-B==>C
  | Rimpl_e Γ B C : Γ:-B==>C -> Γ:-B -> Γ:-C
  | Rforall_i Γ B : (clift 1 Γ 0):-B -> Γ:-(Fforall B)
  | Rforall_e Γ B t : Γ:-(Fforall B) -> Γ:-(fsubst 0 t B)
  | Rexists_i Γ B t : Γ:-(fsubst 0 t B) -> Γ:-(Fexists B)
  | Rexists_e Γ A B :
    Γ:-(Fexists B) -> (B::clift 1 Γ 0):-(flift 1 A 0) -> Γ:-A

where "Γ :- A" := (rule Γ A).

(* Auxiliary connectives and admissible rules *)

(* TODO: define the following formulas *)
Definition Ftrue := Ffalse ==> Ffalse.
Definition Fnot A := (A ==> Ffalse)%pa.
Definition Fiff A B := ((A ==> B) /\ (B ==> A))%pa.

(* n repeated forall *)
Fixpoint nFforall n :=
  match n with
    | 0 => (fun A => A)
    | S m => (fun A => Fforall (nFforall m A))
  end. 

Notation "~ A" := (Fnot A) : pa_scope.

Lemma Rtrue_i : forall Γ, Γ:-Ftrue.
Proof.
  intros; unfold Ftrue; apply Rimpl_i; 
  constructor; intuition.
Qed.

Lemma Rnot_i : forall Γ A, (A::Γ):-Ffalse -> Γ:- ~A.
Proof.
  intros; unfold Fnot; now constructor.
Qed.

Lemma Rnot_e : forall Γ A, Γ:-A -> Γ:- ~A -> Γ:-Ffalse.
Proof.
  unfold Fnot; intros; now apply Rimpl_e with (B:=A).
Qed.

Lemma Riff_i : forall Γ A B,
  (A::Γ):-B -> (B::Γ):-A -> Γ:-(Fiff A B).
Proof.
  unfold Fiff; intros; apply Rimpl_i in H;
  apply Rimpl_i in H0; now constructor.
Qed.

Lemma nFforall_1 : forall n x t A,
  fsubst x t (nFforall n A) = nFforall n (fsubst (n + x) t A).
Proof.
  induction n.
  - auto.
  - intros; simpl; f_equal.
    assert (S (n + x) = n + S x); auto.
    rewrite H; apply IHn with (x := S x) (A := A) (t := t).
Qed.

(* Peano axioms *)

Inductive PeanoAx : formula -> Prop :=
  | pa_refl : PeanoAx (nFforall 1 (#0 = #0))
  | pa_sym : PeanoAx (nFforall 2 (#1 = #0 ==> #0 = #1))
  | pa_trans : PeanoAx (nFforall 3 (#2 = #1 /\ #1 = #0 ==> #2 = #0))
  | pa_compat_s : PeanoAx (nFforall 2 (#1 = #0 ==> Tsucc #1 = Tsucc #0))
  | pa_compat_plus_l : PeanoAx (nFforall 3 (#2 = #1 ==> #2 + #0 = #1 + #0))
  | pa_compat_plus_r : PeanoAx (nFforall 3 (#1 = #0 ==> #2 + #1 = #2 + #0))
  | pa_compat_mult_l : PeanoAx (nFforall 3 (#2 = #1 ==> #2 * #0 = #1 * #0))
  | pa_compat_mult_r : PeanoAx (nFforall 3 (#1 = #0 ==> #2 * #1 = #2 * #0))
  | pa_plus_O : PeanoAx (nFforall 1 (Tzero + #0 = #0))
  | pa_plus_S : PeanoAx (nFforall 2 (Tsucc #1 + #0 = Tsucc (#1 + #0)))
  | pa_mult_O : PeanoAx (nFforall 1 (Tzero * #0 = Tzero))
  | pa_mult_S : PeanoAx (nFforall 2 (Tsucc #1 * #0 = (#1 * #0) + #0))
  | pa_inj : PeanoAx (nFforall 2 (Tsucc #1 = Tsucc #0 ==> #1 = #0))
  | pa_discr : PeanoAx (nFforall 1 (~ Tzero = Tsucc #0))
  | pa_ind : forall A n, cformula (S n) A ->
    PeanoAx (nFforall n (
      fsubst 0 Tzero A /\
      Fforall (A ==> fsubst 0 (Tsucc #0) (flift 1 A 1)) ==> Fforall A
    )).

(* Definition of theorems over Heyting Arithmetic.

   NB: we should normally restrict theorems to closed terms only,
   but this doesn't really matter here, since we'll only prove that
   False isn't a theorem. *)

Definition Thm T :=
  exists axioms, (forall A, In A axioms -> PeanoAx A) /\ (axioms:-T).

(* Example of theorem *)

Lemma HA_n_Sn : Thm (Fforall (~ #0 = Tsucc #0)).
Proof.
  Definition Gamma :=  nFforall 0 (
                      fsubst 0 Tzero (~ #0 = Tsucc #0) /\
                      Fforall ((~ #0 = Tsucc #0)
                               ==> fsubst 0 (Tsucc #0) (flift 1 (~ #0 = Tsucc #0) 1))
                               ==> Fforall (~ #0 = Tsucc #0) )
            :: nFforall 2 (Tsucc #1 = Tsucc #0 ==> #1 = #0)
            :: nFforall 1 (~ Tzero = Tsucc #0)
            :: nil.
  exists Gamma.
  split.
  (* (forall A, In A axioms -> PeanoAx A) *)
  - intros; repeat (destruct H; try apply pa_ind;
    try apply pa_inj; try apply pa_discr; try constructor; eauto).
  
  (* (axioms:-T) *)

  (* hyp is to make the proof terms more readable. This is just implication
  elimination in the induction principle*)
  Definition hyp := nFforall 0 (fsubst 0 Tzero (~ #0 = Tsucc #0) /\
                    Fforall ((~ #0 = Tsucc #0)
                               ==> fsubst 0 (Tsucc #0)
                               (flift 1 (~ #0 = Tsucc #0) 1))).
  - apply Rimpl_e with hyp.
    + apply Rax; simpl; auto.
    + simpl; apply Rand_i; simpl.
      assert ((Tzero = Tsucc Tzero ==> Ffalse) = (fsubst 0 Tzero (~ Tzero = Tsucc #0)));
          auto; rewrite H; apply Rforall_e; constructor; simpl; auto.
      apply Rforall_i; apply Rimpl_i; apply Rimpl_i;
      apply (@Rimpl_e _ (# 0 = Tsucc # 0) Ffalse).
      constructor; simpl; auto.
      apply (@Rimpl_e _ (Tsucc # 0 = Tsucc (Tsucc # 0)) (# 0 = Tsucc # 0)).
      assert ((Tsucc # 0 = Tsucc (Tsucc # 0) ==> # 0 = Tsucc # 0)
          = (fsubst 0 (Tsucc #0) (Tsucc #1 = Tsucc #0  ==> # 1 = # 0)));
          simpl; auto.
          rewrite H; apply Rforall_e.
      assert ( (Fforall (Tsucc # 1 = Tsucc # 0 ==> # 1 = # 0))
          = fsubst 0 #0 (Fforall (Tsucc # 1 = Tsucc # 0 ==> # 1 = # 0))).
          simpl; auto.
      rewrite H0; apply Rforall_e;
      constructor; simpl; auto.
      constructor; simpl; auto.
Qed.

(* Interpretation of terms, using a valuation for variables *)

Definition valuation := list nat.

Fixpoint tinterp (v:valuation) t :=
  match t with
    | Tvar j => nth j v O
    | Tzero => O
    | Tsucc t => S (tinterp v t)
    | Tplus t t' => tinterp v t + tinterp v t'
    | Tmult t t' => tinterp v t * tinterp v t'
  end.

Lemma tlift_unit: forall t n, tlift 0 t n = t.
Proof.
  induction t; intros; 
  repeat (simpl; auto; break);
  simpl; try f_equal; 
  try apply IHt; try apply IHt1; try apply IHt2.
Qed.

Lemma tinterp_1 : forall t v0 v1 v2,
  tinterp (v0++v1++v2) (tlift (length v1) t (length v0)) =
  tinterp (v0++v2) t.
Proof.
  intros; induction t;
  simpl; try break; auto.
  repeat rewrite app_nth2;
  f_equal; auto.
  repeat rewrite app_nth1; auto.
Qed.

Set Printing All.

Lemma tinterp_2 : forall t' t v1 v2,
  tinterp (v1 ++ v2) (tsubst (length v1) t' t) =
  tinterp (v1 ++ (tinterp v2 t') :: v2) t.
Proof.
  intros; induction t;
  simpl;
  try destruct (nat_compare_spec (length v1) n); auto.
  - rewrite <- (app_nil_l v1); repeat rewrite <- app_assoc.
    assert (length (nil ++ v1) = length v1); auto; rewrite H0.
    assert (@length nat nil = 0); auto; rewrite <- H1.
    rewrite (tinterp_1 t' nil v1 v2); simpl.
    assert (n - length v1 = 0); auto.
    rewrite (app_nth2 v1 (tinterp v2 t' :: v2) 0);
    simpl. rewrite H2; auto. auto.
  - rewrite (app_nth2 v1 (tinterp v2 t' :: v2) 0); auto.
    unfold tinterp at 1.
    rewrite (app_nth2 v1 v2 0); auto.
    assert (tinterp v2 t' :: v2 = ((tinterp v2 t')::nil) ++ v2); auto.
    rewrite H0; rewrite (app_nth2 _ v2 0);
    assert (length (tinterp v2 t' :: nil) = 1); auto; rewrite H1.
    assert (Init.Nat.pred n - length v1 = n - length v1 - 1); auto;
    rewrite H2; auto.
  - simpl; repeat rewrite app_nth1; auto.
Qed.

(* Interpretation of formulas *)

Fixpoint finterp v A :=
  match A with
    | Fequal t t' => tinterp v t = tinterp v t'
    | Ffalse => False
    | Fand B C => finterp v B /\ finterp v C
    | For B C => finterp v B \/ finterp v C
    | Fimplies B C => finterp v B -> finterp v C
    | Fexists B => exists n, finterp (n::v) B
    | Fforall B => forall n, finterp (n::v) B
  end.

Lemma finterp_1 : forall A v0 v1 v2,
  finterp (v0 ++ v1 ++ v2) (flift (length v1) A (length v0)) <->
  finterp (v0 ++ v2) A.
Proof.
  intros. revert v0 v1 v2. induction A;  intros.
  - simpl. split;intros.
    + simpl in H. repeat(rewrite tinterp_1 in H). assumption.
    + repeat (rewrite tinterp_1). assumption.
  - auto. simpl. split;auto.
  - split; intro; destruct H; apply (IHA1 v0 v1 v2) in H;
    split ; try apply (IHA2 v0 v1 v2) in H0 ; assumption.
  - split ; intro; destruct H.
    +left. simpl in H. apply (IHA1 v0 v1 v2) in H. assumption.
    +right. apply (IHA2 v0 v1 v2) in H. assumption.
    +left. simpl in H. apply (IHA1 v0 v1 v2) in H. assumption.
    +right. apply (IHA2 v0 v1 v2) in H. assumption.

  - split;intro; simpl in H; simpl; intro; apply (IHA1 v0 v1 v2) in H0;
    apply H in H0; apply (IHA2 v0 v1 v2) in H0; assumption.

  - split; intro; simpl; simpl in H; destruct H; exists x; rewrite app_comm_cons;
    apply (IHA (x::v0)v1 v2); assumption.
  -split; intro; simpl;simpl in H; intro; rewrite app_comm_cons;
   apply (IHA (n::v0)v1 v2); apply H.

Qed.

Lemma finterp_2 : forall t' A v1 v2,
  finterp (v1 ++ v2) (fsubst (length v1) t' A) <->
  finterp (v1 ++ (tinterp v2 t') :: v2) A.
Proof.
  intros; revert v1 v2; induction A; intros;
  simpl; split; intuition;
  repeat rewrite <- tinterp_2; auto;
  repeat rewrite tinterp_2; auto;
  try apply (@IHA1 v1 v2) in H0; intuition;
  try apply (@IHA2 v1 v2) in H1; intuition;
  try apply (@IHA2 v1 v2) in H0; intuition;
  try (destruct H; exists x; rewrite app_comm_cons; apply (@IHA (x::v1) v2)); auto;
  try (apply (@IHA (n::v1) v2); rewrite <- app_comm_cons); intuition.
Qed.

(* Interpretation of contexts *)

Definition cinterp v Γ := forall A, In A Γ -> finterp v A.

(* Soundess of deduction rules *)

Lemma f_to_c : forall v A Γ , finterp v A ->  cinterp v Γ -> cinterp v (A :: Γ).
Proof.
  intros. unfold cinterp in *. intros.
  simpl in H1. destruct H1; try rewrite <- H1; auto .
Qed.


Lemma for_soundness_misc : forall Γ (A:formula) B, In A Γ -> In A (B::Γ).
Proof.
  intros. simpl. auto.
Qed.


(*this lemma is useful for cinterp_1 and soundness_rules*)
Lemma soundness_misc : forall Γ A m n, In A (clift m Γ n) -> 
                                        exists B, A = flift m B n /\ In B Γ.
Proof.
  intros. induction Γ; simpl in H; try contradiction.
  simpl in H. destruct H.
  - exists a. split; try simpl; auto.
           - assert (exists B : formula, A = flift m B n /\ In B Γ). auto.
             destruct H0 as [B H0]. exists B. destruct H0.
             split ; try apply for_soundness_misc; auto.
Qed.


(*added by Alice*)
(*I hope this is true*)
Lemma cinterp_1 : forall Γ v0 v1 v2,
                    cinterp (v0 ++ v2) Γ ->
                    cinterp (v0 ++ v1 ++ v2) (clift (length v1) Γ (length v0)) .
                    
Proof.
  intro. induction Γ.
  - intros. simpl. unfold cinterp. intros. simpl in H0. contradiction.    
  -  unfold cinterp.  simpl. intros. destruct H0.
     + rewrite <- H0. apply finterp_1. apply H. auto.
     + assert (exists B, A = flift (length v1) B (length v0)/\ In B Γ).
       apply soundness_misc. auto.
       destruct H1 as [B H1]. destruct H1. rewrite H1. apply finterp_1.
       apply H. auto.
Qed.


Lemma finterp_misc  : forall v t B,  finterp v (fsubst 0 t B) <->
                                     (exists n, finterp (n::v) B).
Admitted.

Lemma finterp_misc_2 :  forall v A, 
  (exists n, (finterp (n :: v) (flift 1 A 0))) ->
  finterp v A.
Proof.
  intros.
   destruct H as [n H].
    assert (finterp ((nil : list nat) ++ (n :: nil) ++ v)
                    (flift (length (n :: nil)) A (length (nil : list nat))) <->
            finterp ((nil : list nat) ++ v) A).
  - apply finterp_1.
  - simpl in H0. apply H0. auto.
   
Qed.


Lemma finterp_misc_3 :  forall n v A, 
                          finterp v A ->
                          (finterp (n :: v) (flift 1 A 0)).
Proof.
  intros. assert (finterp ((nil : list nat) ++ (n :: nil) ++ v)
                          (flift (length (n :: nil)) A
                                 (length (nil : list nat))) <->
                  finterp ((nil : list nat) ++ v) A).
  - apply finterp_1.
  - simpl in H0. apply H0. auto.
Qed.


(*Particular case of cinterp1*)
Lemma cinterp_forall : forall Γ n v , cinterp v Γ ->
                                      cinterp (n :: v) (clift 1 Γ 0).
Proof.

  intros. assert (cinterp ( nil ++(n::nil) ++ v)
                          (clift (length (n::nil))  Γ (length (nil:list nat)))).
  - apply (cinterp_1  Γ nil (n::nil) v). simpl. auto.
  - simpl in H0. auto.
Qed.



Lemma soundness_rules : forall Γ A, Γ:-A ->
  forall v, cinterp v Γ -> finterp v A.
Proof.
  (*intros. apply yeswecan with Γ. auto.*)
  intro;intro;intro.  induction H.
  - intros. apply H0. auto.
  - intros. cut False. auto. simpl in IHrule. apply IHrule with v. auto.
  - simpl. split; auto.
  - simpl in IHrule. apply IHrule. 
  - simpl in IHrule. apply IHrule. 
  - simpl. left. auto.
  - simpl. right. auto.
  - intros. simpl in IHrule1. assert (finterp v B \/ finterp v C); auto.
    destruct H3.
    + apply IHrule2. apply f_to_c; auto.
    + apply IHrule3. apply f_to_c; auto.
  - simpl. intros. apply IHrule. apply f_to_c; auto.
  - simpl in IHrule1. auto.
  - simpl. intros. apply IHrule. apply cinterp_forall. auto.
  - intros. simpl in IHrule. simpl.
    apply finterp_misc . exists 0. auto.
  - intros. simpl. apply finterp_misc with t . auto.
  - intros. unfold cinterp in IHrule2. simpl in *. apply finterp_misc_2.
    assert (exists n, finterp (n::v) B). auto.
    destruct H2. exists x.
    apply IHrule2 . intros. destruct H3.
    + rewrite <- H3. auto.
    + assert (exists C, A0 = flift 1 C 0 /\ In C Γ). apply soundness_misc. auto.
      destruct H4 as [C H4]. destruct H4.
      assert (finterp v C). auto. rewrite H4.
      apply finterp_misc_3. auto.
Qed.                 

                                       
    
Lemma soundness_axioms : forall A, PeanoAx A -> forall v, finterp v A.
Proof.
  intros.  induction H; induction v; simpl; auto.
  - induction n; simpl;auto.

Admitted.


Theorem soundness : forall A, Thm A -> forall v, finterp v A.
Proof.
  intro; intro. repeat (destruct H). intro. apply soundness_rules with x. auto.
  unfold cinterp. intros. apply soundness_axioms. auto.
 Qed.
    
Theorem coherence : ~Thm Ffalse.
Proof.
  intro.
  assert (finterp nil  Ffalse).
  apply soundness; auto.
  simpl in H0; auto.
Qed.

