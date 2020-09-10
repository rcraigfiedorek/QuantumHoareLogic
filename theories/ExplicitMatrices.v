
Require Export QNLAlt.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Setoid.
Require Import NArith.


(*
Definition Row (n:nat) := nat -> C.
Definition entry c : Row 1 := fun _ => c.
Definition entry_append_l {n} (x : Row n) (c:C) : Row (S n) :=
  fun j =>  match j with
            | O => c
            | S j => x j
            end.
Definition rowmat {n} (x : Row n) : Matrix 1 n := fun _ => x.
Definition row_append_u {m n} (M : Matrix m n) (x : Row n) :=
  fun i =>  match i with
            | O => x
            | S i => M i
            end.

Notation "[ c ]" := (entry c) : matrix_scope.
Notation "[ a , b , .. , c , d ]" := (entry_append_l a (entry_append_l b .. (entry_append_l c (entry d)) ..)) (at level 10, a at level 0, b at level 0, c at level 0, d at level 0) : matrix_scope.
Notation "'{[' x ']}'" := (rowmat x) : matrix_scope.
Notation "'{[' w , x , .. , y , z ']}'" := (row_append_u w (row_append_u x .. (row_append_u y (rowmat z)) ..)) (at level 20, w at level 10, x at level 10, y at level 10, z at level 10) : matrix_scope.
*)
Open Scope N_scope.
Open Scope matrix_scope.

Section yeah.

Context {n:N}.

Definition twobytwo a b c d : Square 2 := fun i j =>
  match i with
  | 0 => match j with
         | 0 => a
         | _ => b
         end
  | _ => match j with
         | 0 => c
         | _ => d
         end
  end.

Arguments twobytwo (a b c d)%C.
Arguments twobytwo (a b c d)%R : extra scopes.

Definition bitProj0 := twobytwo 1 0 0 0.

Definition bitProj1 := twobytwo 0 0 0 1.

Definition id2 := twobytwo 1 0 0 1.

Lemma id2_I2 : id2 == I 2.
Proof. mintros. unfold I; destruct i; destruct j; simpl; try auto.
assert (p = p0) by nomega; subst; rewrite Pos.eqb_refl. auto.
Qed.

Definition pauliX := twobytwo 0 1 1 0.
Definition pauliY := twobytwo 0 (-Ci)%C Ci 0.
Definition pauliZ := twobytwo 1 0 0 (-1).
Definition Hdmrd := (/√2) .* twobytwo 1 1 1 (-1).

Lemma Mmult_id2_l : forall {m}(A: Matrix 2 m), id2 × A == A.
Proof. intros. rewrite id2_I2. apply Mmult_1_l. Qed.

Lemma Mmult_id2_r : forall {m}(A: Matrix m 2), A × id2 == A.
Proof. intros. rewrite id2_I2. apply Mmult_1_r. Qed.

Definition qubitgate (tbit : N)(U : Square 2)`{Unitary _ U} : Square (2^n) :=
  tensor n (fun k => if (k =? tbit) then U else id2).

Definition cgate (cbit tbit : N)(U : Square 2)`{Unitary _ U} : Square (2^n) :=
  tensor n (fun k => if (k =? cbit) then bitProj0 else id2)
    .+ tensor n (fun k => if (k =? cbit) then bitProj1 else if (k =? tbit) then U else id2).




Theorem cgate_cgate_alt : forall cbit tbit U `{Unitary _ U}, cbit <> tbit -> cbit < n -> tbit < n ->
  cgate cbit tbit U == cgate_alt cbit tbit U.
Proof. intros. mintros. unfold cgate.
destruct (N.testbit i cbit) eqn:He.
- 







Definition matrix_from_Nfunc (f : N -> N) : Square (2^n) := fun i j =>
  if (j =? (f i)) then C1 else C0.

Theorem matrix_Nfunc_comp : forall f g,
  (forall i, (i < 2^n -> f i < 2^n)%N) ->
    (matrix_from_Nfunc f) × (matrix_from_Nfunc g) == matrix_from_Nfunc (fun i => g (f i)).
Proof.
intros. unfold matrix_from_Nfunc, Mmult; intros i j Hi Hj.
destruct (j =? g (f i)) eqn:H1.
  - apply Csum_unique with (f i). apply H; auto. rewrite N.eqb_refl; rewrite H1; lca.
    intros. replace (x' =? f i) with false; [lca|]. symmetry; apply N.eqb_neq; auto.
  - apply Csum_0. intros. destruct (N.eq_dec x (f i)). subst. rewrite H1; lca.
    replace (x =? f i) with false; [lca|symmetry; apply N.eqb_neq; auto].
Qed.


Definition cnot_N (cbit tbit : N) (x : N) : N :=
  if (N.testbit x cbit) then (N.lxor x (2^tbit)) else x.

Definition cnot (cbit tbit : N) := matrix_from_Nfunc (cnot_N cbit tbit).

Lemma cnot_N_involutive : forall cbit tbit x, cbit <> tbit -> cbit < n -> tbit < n -> x < 2^n ->
  cnot_N cbit tbit (cnot_N cbit tbit x) = x.
Proof.
intros. unfold cnot_N. assert (N.testbit (N.lxor x (2^tbit)) cbit = N.testbit x cbit).
  { rewrite N.lxor_spec. rewrite N.pow2_bits_eqb. replace (_=?_) with false. apply Bool.xorb_false_r. symmetry; apply N.eqb_neq; auto. }
destruct (N.testbit x cbit) eqn: H4.
  + rewrite H3; simpl. rewrite N.lxor_assoc. rewrite N.lxor_nilpotent. apply N.lxor_0_r.
  + rewrite H4. auto.
Qed.

Lemma cnot_N_bounded : forall cbit tbit x, cbit <> tbit -> cbit < n -> tbit < n ->
  x < 2^n -> cnot_N cbit tbit x < 2^n.
Proof.
intros. unfold cnot_N. destruct (N.testbit x cbit) eqn:H3; try auto.
apply N.log2_lt_cancel. eapply N.le_lt_trans.
apply N.log2_lxor. apply N.max_lub_lt. apply N.log2_lt_pow2.
destruct x. easy. easy. rewrite N.log2_pow2. 1,2:nomega. repeat rewrite N.log2_pow2; nomega.
Qed.



(* ******* *)

Instance cnot_herm : forall cbit tbit,
  cbit <> tbit -> cbit < n -> tbit < n -> Hermitian (cnot cbit tbit).
Proof.
  split. unfold adjoint, cnot, matrix_from_Nfunc; intros i j Hi Hj.
  destruct (j =? cnot_N cbit tbit i) eqn:H2.
    - replace j with (cnot_N cbit tbit i); [|symmetry; apply N.eqb_eq; auto].
      rewrite cnot_N_involutive; eauto. rewrite N.eqb_refl. lca.
    - assert (i =? cnot_N cbit tbit j = false). apply N.eqb_neq. intro IC.
      rewrite IC in H2. rewrite cnot_N_involutive in H2; eauto. rewrite N.eqb_refl in H2. inversion H2.
      rewrite H3; lca.
Qed.

Instance cnot_unitary : forall cbit tbit,
  cbit <> tbit -> cbit < n -> tbit < n -> Unitary (cnot cbit tbit).
Proof.
split. rewrite <- (@cond_hermitian _ (cnot _ _)). unfold cnot; rewrite matrix_Nfunc_comp.
unfold matrix_from_Nfunc. intros i j Hi Hj. rewrite cnot_N_involutive. unfold I. rewrite N.eqb_sym.
all:try easy. intros. apply cnot_N_bounded. all:try eauto. apply cnot_herm; auto.
Qed.


(* do work with tensor product of transformations now *)
(* define new / theorize properties of kron products of matrices
with dimensions that are powers of 2? *)


Close Scope N_scope.

Open Scope C_scope.

Definition id2 := twobytwo 1 0 0 1.


Theorem hdmrd_sqr : Hdmrd × Hdmrd == id2.
Proof. unfold Mmult, Hdmrd, id2, Mscale; mintros; destruct i; destruct j; simpl; try lca.

pose proof Csqrt2_square.
repeat rewrite Cmult_1_r. field_simplify. rewrite H. lca. unfold sqrt. Print  Rcase_abs. rewrite sqrt2_neq_0.



Definition BoolVect (n:nat) := nat -> bool.
Definition BoolLinMap (n:nat) := BoolVect n -> BoolVect n.

Definition bool_CNOT n i j : BoolLinMap n := fun v =>
  if (v i) then v else (fun k => if (Nat.eqb k j) then (negb (v k)) else (v k)).

(*
Class InvBoolLinMap (n:nat) := {
  *)
(* prove bool_CNOT is invertible, so is composition of invertibles, then
that mapping to matrices gives unitary (also permutation if we ever need that) *)


(* eek *)
(* we gotta rework everything around BinInt, not Nat *)


Definition nat_boolvect_correspondence (n:nat)(i:nat) : BoolVect n :=
  fun k => 

Definition blm_to_matrix {n}(T:BoolLinMap n) : Matrix (2^n) :=
  fun i j









