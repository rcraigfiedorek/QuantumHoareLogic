(** * Complex: Complex Numbers in Coq *)
(** * This file is largely borrowed from Robert Rand's
      Verified Quantum Computing book
      http://www.cs.umd.edu/~rrand/vqc/Complex.html *)

Require Export Reals.
Require Export Psatz.
Require Import Omega.

Open Scope R_scope.
Notation "√ n" := (sqrt n) (at level 20) : R_scope.

(* ################################################################# *)
(** * Basic Definitions *)

Definition C : Type := R * R.

Definition C0 : C := (0,0).
Definition C1 : C := (1,0).
Definition Ci : C := (0,1).

Definition RtoC (r : R) : C := (r,0).

Coercion RtoC : R >-> C.

Definition Cplus (c1 c2 : C) : C := (fst c1 + fst c2, snd c1 + snd c2).

Definition Copp (c : C) : C := (- fst c, - snd c).
Definition Cminus (c1 c2 : C) : C := Cplus c1 (Copp c2).

Definition Cmult (c1 c2 : C) : C :=
    (fst c1 * fst c2 - snd c1 * snd c2, fst c1 * snd c2 + snd c1 * fst c2).

Definition Cinv (c : C) : C :=
  (fst c / (fst c ^ 2 + snd c ^ 2), - snd c / (fst c ^ 2 + snd c ^ 2)).

Definition Cdiv (c1 c2 : C) : C := Cmult c1 (Cinv c2).

Definition Cnorm2 (c : C) : R := fst c ^ 2 + snd c ^ 2. 
Definition Cnorm (c : C) : R := √ (Cnorm2 c).
Arguments Cnorm2 c /.
Arguments Cnorm c /.

Bind Scope C_scope with C.
Delimit Scope C_scope with C.
Infix "+" := Cplus : C_scope.
Notation "- x" := (Copp x) : C_scope.
Infix "-" := Cminus : C_scope.
Infix "*" := Cmult : C_scope.
Notation "/ x" := (Cinv x) : C_scope.
Infix "/" := Cdiv : C_scope.

(* ################################################################# *)
(** * Psatz *)

Lemma c_proj_eq : forall (c1 c2 : C), 
  fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.
Proof. intros. destruct c1, c2. simpl in *. subst. reflexivity. Qed.

Ltac lca := eapply c_proj_eq; simpl; lra.

(* ################################################################# *)
(** * C is a field *)

Open Scope C_scope.

Lemma C1_neq_C0 : C1 <> C0. Proof. intros F. inversion F. lra. Qed.

Lemma Cplus_comm : forall c1 c2 : C, c1 + c2 = c2 + c1. Proof. intros. lca. Qed.
Lemma Cplus_assoc : forall c1 c2 c3 : C, c1 + c2 + c3 = c1 + (c2 + c3).
Proof. intros. lca. Qed.

Lemma Cplus_opp_r : forall c : C, c + - c = 0. Proof. intros. lca. Qed.

Lemma Cplus_0_l : forall c : C, 0 + c = c. Proof. intros. lca. Qed.

Lemma Cmult_comm : forall c1 c2:C, c1 * c2 = c2 * c1. Proof. intros. lca. Qed.

Lemma Cmult_assoc : forall c1 c2 c3:C, c1 * c2 * c3 = c1 * (c2 * c3).
Proof. intros. lca. Qed.

Lemma Cmult_1_l : forall c:C, 1 * c = c. Proof. intros. lca. Qed.

Lemma Cmult_plus_distr_r : forall c1 c2 c3:C, (c1 + c2) * c3 = c1 * c3 + c2 * c3.
Proof. intros. lca. Qed.

Lemma Cinv_l : forall c:C, c <> 0 -> / c * c = 1.
Proof.
  intros.
  eapply c_proj_eq; simpl; unfold Rminus, Rdiv.
  - repeat rewrite <- Ropp_mult_distr_l.
    rewrite Ropp_involutive.
    repeat rewrite Rmult_1_r.
    rewrite (Rmult_comm (fst c)). rewrite Rmult_assoc.
    rewrite (Rmult_comm (snd c) (/ _)). rewrite Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    rewrite Rinv_l; try lra.
    contradict H. apply Rplus_sqr_eq_0 in H. lca.
  - repeat rewrite Rmult_1_r.
    rewrite (Rmult_comm (fst c)). rewrite Rmult_assoc.
    rewrite (Rmult_comm (- snd c)). rewrite Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    lra.
Qed.       

Lemma C_Field_Theory : @field_theory C 0 1 Cplus Cmult Cminus Copp Cdiv Cinv eq.
Proof.
  constructor. constructor.
  (* addition *)
  (* left identity *) apply Cplus_0_l.
  (* commutativity *) apply Cplus_comm.
  (* associativity *) intros; rewrite Cplus_assoc; easy.
  (* multiplication *)
  (* left identity *) apply Cmult_1_l.
  (* commutativity *) apply Cmult_comm.
  (* associativity *) intros; rewrite Cmult_assoc; easy.
  (* distributivity *) apply Cmult_plus_distr_r.
  (* sub = opp *) reflexivity.
  (* additive inverse *) apply Cplus_opp_r.  
  (* 0 <> 1 *) apply C1_neq_C0.
  (* div = inv *) reflexivity.
  (* multiplicative inverse *) apply Cinv_l.
Defined.

Add Field CField : C_Field_Theory.  

(** Some additional useful lemmas *)

Lemma Cplus_opp_l : forall c : C, - c + c = 0. Proof. intros. lca. Qed.
Lemma Cplus_0_r : forall c : C, c + 0 = c. Proof. intros. lca. Qed.
Lemma Cmult_0_l : forall c:C, 0 * c = 0. Proof. intros. lca. Qed.
Lemma Cmult_0_r : forall c:C, c * 0 = 0. Proof. intros. lca. Qed.
Lemma Cmult_1_r : forall c:C, c * 1 = c. Proof. intros. lca. Qed.
Lemma Cmult_plus_distr_l : forall c1 c2 c3:C, c1 * (c2 + c3) = c1 * c2 + c1 * c3.
Proof. intros. lca. Qed.
Lemma Cinv_r : forall c:C, c <> 0 -> c * /c = 1.
Proof. intros. rewrite Cmult_comm. apply Cinv_l. easy. Qed.

Lemma Copp_mult_distr_r : forall c1 c2 : C, - (c1 * c2) = c1 * - c2.
Proof. intros; lca. Qed.
Lemma Copp_mult_distr_l : forall c1 c2 : C, - (c1 * c2) = - c1 * c2.
Proof. intros; lca. Qed.
Lemma Copp_plus_distr : forall c1 c2, - (c1 + c2) = -c1 + (-c2).
Proof. intros; lca. Qed.
Lemma Copp_involutive: forall c : C, - - c = c. Proof. intros; lca. Qed.
  
Lemma Csqrt2_square : √2 * √2 = 2. 
Proof.
  eapply c_proj_eq; simpl; try lra.
  rewrite Rmult_0_r, Rminus_0_r.
  apply sqrt_def.
  lra.
Qed.

Lemma RtoC_neq : forall (r1 r2 : R), r1 <> r2 -> RtoC r1 <> RtoC r2.
Proof. intros r1 r2 H F. inversion F. easy. Qed.

Lemma RtoC_inj : forall (r1 r2 : R), RtoC r1 = RtoC r2 -> r1 = r2.
Proof. intros. inversion H. auto. Qed.

(* ################################################################# *)
(** * The complex conjugate *)

(** One unique operation on complex numbers is the complex conjugate.
    The complex conjugate [c^*] of [c = a + bi] is [a - bi].  This
    operation will frequently appear in a quantum setting in the
    context of the adjoint operation on complex matrices. *)

Definition Cconj (x : C) : C := (fst x, (- snd x)%R).

Notation "a ^*" := (Cconj a) (at level 10) : C_scope.

Lemma Cconj_R : forall r : R, r^* = r.         Proof. intros; lca. Qed.
Lemma Cconj_0 : 0^* = 0.                  Proof. lca. Qed.
Lemma Cconj_opp : forall C, (- C)^* = - (C^*). Proof. reflexivity. Qed.
Lemma Cconj_rad2 : (/ √2)^* = / √2.       Proof. lca. Qed.
Lemma Cconj_involutive : forall c, (c^*)^* = c. Proof. intros; lca. Qed.
Lemma Cconj_plus_distr : forall (x y : C), (x + y)^* = x^* + y^*. Proof. intros; lca. Qed.
Lemma Cconj_mult_distr : forall (x y : C), (x * y)^* = x^* * y^*. Proof. intros; lca. Qed.
Lemma Cconj_mult_norm2 : forall c, c * c^* = Cnorm2 c. Proof. intros; lca. Qed.

Lemma Cnorm2_0_0 : forall c:C, c = 0 <-> Cnorm2 c = 0.
Proof. split; intros. subst; unfold Cnorm2. simpl. field.
unfold Cnorm2 in H. destruct c. simpl in H.
pose proof (pow2_ge_0 r). pose proof (pow2_ge_0 r0).
apply c_proj_eq; simpl.
destruct (Rmult_integral r r);[|auto|auto].
  apply (Rplus_eq_0_l _ (r0*r0)); lra.
destruct (Rmult_integral r0 r0);[|auto|auto].
  apply (Rplus_eq_0_l _ (r*r)); lra.
Qed.

(* ################################################################# *)
(** * Sums over Complex Numbers *)


Require Import NArith.

Ltac nomega := zify; omega.

Definition Csum (f : N -> C) (n : N) : C := 
  @N.recursion C 0 (fun n a => a + (f n)) n.

Lemma Csum_succ : forall f n,
  Csum f (N.succ n) = (Csum f n) + f n.
Proof. intros. unfold Csum at 1. rewrite N.recursion_succ.
fold (Csum f n). auto. auto. unfold Morphisms.Proper, Morphisms.respectful. intros; subst; auto.
Qed.

Lemma Csum_0 : forall (f : N -> C) (n : N),
    (forall x, (x < n)%N -> f x = 0) ->
    Csum f n = 0.
Proof.
  intros f n. N.induct n.
    - reflexivity.
    - intros. rewrite Csum_succ. rewrite H0. rewrite H. lca.
      intros. apply H0.
      1,2: nomega.
Qed.

Lemma Csum_eq : forall (f g : N -> C) (n : N),
  (forall x, (x < n)%N -> f x = g x) ->
  Csum f n = Csum g n.
Proof.
  intros f g n.
  N.induct n; intros; simpl.
  - auto.
  - do 2 rewrite Csum_succ. rewrite H. rewrite H0. auto.
    nomega. intros; apply H0. nomega.
Qed.

Lemma Csum_plus : forall (f g : N -> C) (n : N),
    Csum (fun x => f x + g x) n = Csum f n + Csum g n.  
Proof. 
  intros f g n.
  N.induct n; intros.
  - simpl. lca.
  - repeat rewrite Csum_succ. rewrite H. lca.
Qed.

Lemma Csum_mult_l : forall (c : C) (f : N -> C) (n : N),
    c * Csum f n = Csum (fun x => c * f x) n.
Proof.
  intros c f n.
  N.induct n; intros.
  - simpl; lca.
  - repeat rewrite Csum_succ.
    rewrite Cmult_plus_distr_l.
    rewrite H. auto.
Qed.

Lemma Csum_mult_r : forall (c : C) (f : N -> C) (n : N),
    Csum f n * c = Csum (fun x => f x * c) n.
Proof.
  intros c f n.
  N.induct n; intros.
  - simpl; lca.
  - repeat rewrite Csum_succ.
    rewrite Cmult_plus_distr_r.
    rewrite H. auto.
Qed.

Lemma Csum_order : forall (f : N -> N -> C) (m n : N),
  Csum (fun x => Csum (f x) n) m = Csum (fun y => Csum (fun x => f x y) m) n.
Proof.
  intros. N.induct m; intros; simpl; repeat rewrite Csum_succ; simpl.
    rewrite Csum_0; [field | auto].
    rewrite H. rewrite <- Csum_plus.
    apply Csum_eq; intros. rewrite Csum_succ. auto.
Qed.

Lemma Csum_conj_distr : forall (f : N -> C) (n : N),
    (Csum f n) ^* = Csum (fun x => (f x)^*) n.
Proof.
  intros. N.induct n; intros.
  - simpl. lca.
  - rewrite Csum_succ. rewrite Cconj_plus_distr. rewrite H.
    rewrite Csum_succ. auto.
Qed.

Lemma Csum_unique : forall (f : N -> C) (k : C) (n x : N), 
  (x < n)%N ->
  f x = k ->
  (forall x', x <> x' -> f x' = 0) ->
  Csum f n = k.
Proof.
  intros f k n; N.induct n; intros.
  - nomega.
  - rewrite Csum_succ. destruct (N.eq_dec n x).
    + subst. rewrite Csum_0. lca. intros; apply H2. nomega.
    + rewrite H2. rewrite (H x). lca. all:eauto; nomega.
Qed.

Lemma Csum_split : forall (f g : N -> C) (m n : N),
  (Csum f m) + (Csum g n) = Csum (fun i => if (i <? m)%N then f i else g (i - m)%N) (m + n).
Proof.
intros f g m. apply N.peano_ind.
- simpl. rewrite N.add_0_r. rewrite Cplus_0_r. apply Csum_eq.
  intros. destruct (x <? m)%N eqn:H1. auto. exfalso. pose proof (N.ltb_nlt x m). apply H0; auto.
- intros. rewrite Csum_succ. rewrite <- Cplus_assoc. rewrite H. rewrite N.add_succ_r.
  rewrite Csum_succ. destruct (N.eq_dec n 0). subst. repeat rewrite N.add_0_r. rewrite N.ltb_irrefl.
  rewrite N.sub_diag; auto. replace (m + n <? m)%N with false. apply f_equal2. auto. apply f_equal; nomega.
  symmetry. apply N.ltb_ge. nomega.
Qed.

Definition Cprod (f : N -> C) (n : N) : C := 
  @N.recursion C 1 (fun n a => a * (f n)) n.

Lemma Cprod_succ : forall f n,
  Cprod f (N.succ n) = (Cprod f n) * f n.
Proof. intros. unfold Cprod at 1. rewrite N.recursion_succ.
fold (Cprod f n). auto. auto. unfold Morphisms.Proper, Morphisms.respectful. intros; subst; auto.
Qed.

Lemma Cprod_1 : forall (f : N -> C) (n : N),
    (forall x, (x < n)%N -> f x = 1) ->
    Cprod f n = 1.
Proof.
  intros f n. N.induct n.
    - reflexivity.
    - intros. rewrite Cprod_succ. rewrite H0. rewrite H. lca.
      intros. apply H0.
      1,2: nomega.
Qed.

Lemma Cprod_0 : forall f n, (exists x, (x < n)%N /\ f x = 0) -> Cprod f n = 0.
Proof. intros f n. N.induct n; intros.
- induction H. nomega.
- induction H0. induction H0. destruct (N.eq_dec x n).
  + subst. rewrite Cprod_succ. rewrite H1; lca.
  + rewrite Cprod_succ. rewrite H. lca. exists x. split. nomega. auto.
Qed.

Lemma Cprod_eq : forall (f g : N -> C) (n : N),
  (forall x, (x < n)%N -> f x = g x) ->
  Cprod f n = Cprod g n.
Proof.
  intros f g n.
  N.induct n; intros; simpl.
  - auto.
  - do 2 rewrite Cprod_succ. rewrite H. rewrite H0. auto.
    nomega. intros; apply H0. nomega.
Qed.

Lemma Cprod_mult : forall (f g : N -> C) (n : N),
    Cprod (fun x => f x * g x) n = Cprod f n * Cprod g n.
Proof. 
  intros f g n.
  N.induct n; intros.
  - simpl. lca.
  - repeat rewrite Cprod_succ. rewrite H. lca.
Qed.

(*
Lemma Csum_mult_l : forall (c : C) (f : N -> C) (n : N),
    c * Csum f n = Csum (fun x => c * f x) n.
Proof.
  intros c f n.
  N.induct n; intros.
  - simpl; lca.
  - repeat rewrite Csum_succ.
    rewrite Cmult_plus_distr_l.
    rewrite H. auto.
Qed.

Lemma Csum_mult_r : forall (c : C) (f : N -> C) (n : N),
    Csum f n * c = Csum (fun x => f x * c) n.
Proof.
  intros c f n.
  N.induct n; intros.
  - simpl; lca.
  - repeat rewrite Csum_succ.
    rewrite Cmult_plus_distr_r.
    rewrite H. auto.
Qed.

Lemma Cprod_order : forall (f : N -> N -> C) (m n : N),
  Csum (fun x => Csum (f x) n) m = Csum (fun y => Csum (fun x => f x y) m) n.
Proof.
  intros. N.induct m; intros; simpl; repeat rewrite Csum_succ; simpl.
    rewrite Csum_0; [field | auto].
    rewrite H. rewrite <- Csum_plus.
    apply Csum_eq; intros. rewrite Csum_succ. auto.
Qed.

Lemma Csum_conj_distr : forall (f : N -> C) (n : N),
    (Csum f n) ^* = Csum (fun x => (f x)^* ) n.
Proof.
  intros. N.induct n; intros.
  - simpl. lca.
  - rewrite Csum_succ. rewrite Cconj_plus_distr. rewrite H.
    rewrite Csum_succ. auto.
Qed.

Lemma Csum_unique : forall (f : N -> C) (k : C) (n x : N), 
  (x < n)%N ->
  f x = k ->
  (forall x', x <> x' -> f x' = 0) ->
  Csum f n = k.
Proof.
  intros f k n; N.induct n; intros.
  - nomega.
  - rewrite Csum_succ. destruct (N.eq_dec n x).
    + subst. rewrite Csum_0. lca. intros; apply H2. nomega.
    + rewrite H2. rewrite (H x). lca. all:eauto; nomega.
Qed.

Lemma Csum_split : forall (f g : N -> C) (m n : N),
  (Csum f m) + (Csum g n) = Csum (fun i => if (i <? m)%N then f i else g (i - m)%N) (m + n).
Proof.
intros f g m. apply N.peano_ind.
- simpl. rewrite N.add_0_r. rewrite Cplus_0_r. apply Csum_eq.
  intros. destruct (x <? m)%N eqn:H1. auto. exfalso. pose proof (N.ltb_nlt x m). apply H0; auto.
- intros. rewrite Csum_succ. rewrite <- Cplus_assoc. rewrite H. rewrite N.add_succ_r.
  rewrite Csum_succ. destruct (N.eq_dec n 0). subst. repeat rewrite N.add_0_r. rewrite N.ltb_irrefl.
  rewrite N.sub_diag; auto. replace (m + n <? m)%N with false. apply f_equal2. auto. apply f_equal; nomega.
  symmetry. apply N.ltb_ge. nomega.
Qed.*)




(*
Definition fin_bij (f : N -> N) (n : N) : Prop :=
  (forall x, (x < n)%N -> (f x < n)%N) /\
    (forall x y, (x < n)%N -> (y < n)%N -> f x = f y -> x = y).

Lemma fin_bij_surj : forall f n, fin_bij f n ->
  forall y, (y < n)%N -> exists x, (x < n)%N /\ f x = y.
Proof.
intros f n. N.induct n; intros.
- nomega.
- induction H0. destruct (N.eq_dec (f n) n).
  + subst. destruct (N.eq_dec y n).
    -- subst. exists n. auto.
    -- assert (fin_bij f n). split. intros. specialize (H0 _ (N.lt_lt_succ_r _ _ H3)).
Admitted.



Lemma Csum_bij : forall (f : N -> C) (n : N) (pi : N -> N),
  fin_bij pi n -> Csum f n = Csum (fun x => f (pi x)) n.
Proof.
intros f n. N.induct n; intros.
- reflexivity.
- do 2 rewrite Csum_succ. induction H0.
  assert (fin_bij pi n \/ exists x, pi x = n).
  + unfold fin_bij. Search ((_ /\ _) \/ _ ).
Admitted.*)

Lemma Csum_convolution : forall (f g : N -> C) (m n : N),
  (Csum f m) * (Csum g n) = Csum (fun i => (f (i / n)%N) * (g (i mod n)%N)) (m * n).
Proof.
intros. rewrite Csum_mult_r.
rewrite (Csum_eq (fun x : N => f x * Csum g n) (fun x => Csum (fun y => (f x) * (g y)) n)).
2: intros; symmetry; rewrite Csum_mult_l; apply Csum_eq; auto.
N.induct m.
- simpl. auto.
- intros m Hi. rewrite Csum_succ. rewrite Hi. rewrite N.mul_succ_l.
  rewrite Csum_split. apply Csum_eq. intros. destruct (x <? m * n)%N eqn:Heq.
  + auto.
  + assert (m*n <= x)%N by (apply N.ltb_ge; auto). apply f_equal2; apply f_equal.
    apply N.div_unique with (x - m*n)%N. nomega. rewrite N.mul_comm; nomega.
    eapply N.mod_unique. nomega. rewrite N.mul_comm. nomega.
Qed.

Lemma Csum_neg : forall (f : N -> C) (n : N),
    - (Csum f n) = Csum (fun x => - (f x)) n.
Proof. intros; N.induct n; intros; simpl. lca.
repeat rewrite Csum_succ. rewrite Copp_plus_distr. rewrite H. auto.
Qed.

(** We'll make C opaque so Coq doesn't treat it as a pair. *)
Opaque C.

Definition re : C -> R := fst.
Definition im : C -> R := snd.

Lemma Cre_plus : forall c1 c2, (re c1 + re c2)%R = re (c1 + c2).
Proof. intros. destruct c1; destruct c2; simpl; lra. Qed.

Lemma Cre_opp : forall z, (- re z)%R = re(-z).
Proof. intros. destruct z; simpl; lra. Qed.

Definition Clt (c1 c2 : C) : Prop :=
  c1 = c1^* /\ c2 = c2^* /\ re c1 < re c2.

Definition Cle (c1 c2 : C) : Prop :=
  c1 = c1^* /\ c2 = c2^* /\ re c1 <= re c2.

Definition Cgt (c1 c2 : C) : Prop :=
  c1 = c1^* /\ c2 = c2^* /\ re c1 > re c2.

Definition Cge (c1 c2 : C) : Prop :=
  c1 = c1^* /\ c2 = c2^* /\ re c1 >= re c2.

(*Infix "<" := Clt : C_scope.*)
Infix "<=" := Cle : C_scope.
Infix ">" := Cgt : C_scope.
Infix ">=" := Cge : C_scope.
Notation "a '<=' b '<=' c" := (Cle a b /\ Cle b c) : C_scope.

Theorem Creal_conj : forall c, im c = 0 <-> c = c^*.
Proof. unfold Cconj; destruct c as [a b]; split; intros; simpl in *; subst.
  lca. inversion H; lra.
Qed.

Lemma Csum_ge0 : forall (f : N -> C) (n : N),
  (forall x, (x<n)%N -> 0 <= f x) -> 0 <= Csum f n.
Proof.
  intros f n. N.induct n; intros.
  - simpl. split; try lca; split; try lca; lra.
  - simpl. rewrite Csum_succ. split; [|split]. lca.
      rewrite Cconj_plus_distr. f_equal.
        apply H. intros; apply H0. nomega.
        apply H0. auto. nomega.
     apply Rplus_le_le_0_compat. apply H. intros; apply H0; nomega.
     apply H0; nomega.
Qed.

Lemma Cle_0_0 : 0 <= 0.
Proof. repeat split; try lca; lra. Qed.

Lemma Cplus_compat : forall c1 c1' c2 c2',
  c1 = c1' -> c2 = c2' -> c1 + c2 = c1' + c2'.
Proof. intros. rewrite H, H0. auto. Qed.

Lemma Cplus_le_le_0_compat : forall c1 c2,
  0 <= c1 -> 0 <= c2 -> 0 <= c1 + c2.
Proof. intros. repeat split. lca.
rewrite Cconj_plus_distr. apply Cplus_compat.
apply H. apply H0. rewrite <- Cre_plus. apply Rplus_le_le_0_compat.
apply H. apply H0.
Qed.

Lemma Cle_trans : forall c1 c2 c3,
  c1 <= c2 -> c2 <= c3 -> c1 <= c3.
Proof. intros. split;[|split]. apply H. apply H0.
apply Rle_trans with (re c2). apply H. apply H0.
Qed.

Lemma Cplus_le_compat : forall c1 c2 c3 c4,
  c1 <= c2 -> c3 <= c4 -> c1 + c3 <= c2 + c4.
Proof. intros. repeat split. 1,2: rewrite Cconj_plus_distr; apply Cplus_compat;
first [apply H|apply H0]. simpl. apply Rplus_le_compat. apply H. apply H0.
Qed.

Lemma Cplus_eq_0_l : forall c1 c2,
  0 <= c1 -> 0 <= c2 -> c1 + c2 = 0 -> c1 = 0.
Proof. intros. unfold Cle in *. induction H. induction H2. induction H0.
induction H4. induction c1; induction c2. assert (b=0)%R. apply (Creal_conj (a,b)). auto.
assert (a=0)%R. eapply Rplus_eq_0_l. auto. apply H5. subst. inversion H1. symmetry.
rewrite H8; auto. subst; auto.
Qed.

Lemma Cplus_eq_0_r : forall c1 c2,
  0 <= c1 -> 0 <= c2 -> c1 + c2 = 0 -> c2 = 0.
Proof. intros. rewrite Cplus_comm in H1. apply (Cplus_eq_0_l _ c1); eauto.
Qed.

Lemma Csum_nonneg_nonneg : forall (f : N -> C) (n : N),
  (forall x, (x<n)%N -> 0 <= f x) -> 0 <= Csum f n.
Proof. intros f n; N.induct n; intros.
- simpl. apply Cle_0_0.
- rewrite Csum_succ. apply Cplus_le_le_0_compat. apply H. intros.
apply H0. nomega. apply H0. nomega.
Qed.

Lemma Csum_nonneg_0 : forall (f : N -> C) (n : N),
  (forall x, (x<n)%N -> 0 <= f x) -> (Csum f n = 0)
      -> forall x, (x<n)%N -> f x = 0.
Proof. intros f n. N.induct n; intros.
- nomega.
- rewrite Csum_succ in H1. destruct (N.eq_dec x n).
  + rewrite Csum_0 in H1. rewrite Cplus_0_l in H1; subst; auto.
    intros y H3. apply H. intros; apply H0; nomega. apply (Cplus_eq_0_l _ (f n)).
    apply Csum_nonneg_nonneg. intros; apply H0; nomega. apply H0. nomega.
    auto. auto.
  + apply H. intros; apply H0; nomega. apply (Cplus_eq_0_l _ (f n)).
    apply Csum_nonneg_nonneg. intros; apply H0; nomega. apply H0. nomega. auto. nomega.
Qed.


