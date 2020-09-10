(** * Matrix: Lightweight Complex Matrices *)

Require Import Psatz.
Require Import Setoid.
Require Import Arith.
Require Import Bool.
Require Import Program.
Require Export QuantumHoareLogic.Complex.
Require Import Omega.
Require Import NArith.

(** * Matrix Definitions and Equivalence **)

Open Scope N_scope.

(** We define a _matrix_ as a simple function from to nats
    (corresponding to a row and a column) to a complex number. In many
    contexts it would make sense to parameterize matrices over numeric
    types, but our use case is fairly narrow, so matrices of complex
    numbers will suffice. *)
    
Definition Matrix (m n : N) := N -> N -> C.

Notation Vector n := (Matrix n 1).
Notation Square n := (Matrix n n).

(** Note that the dimensions of the matrix aren't being used here. In
    practice, a matrix is simply a function on any two nats. However,
    we will used these dimensions to define equality, as well as the
    multiplication and kronecker product operations to follow. *)

Definition mat_equiv {m n : N} (A B : Matrix m n) : Prop :=
  forall i j, i < m -> j < n -> A i j = B i j.

Infix "==" := mat_equiv (at level 80).

(** Let's prove some important notions about matrix equality. *)

Lemma mat_equiv_refl : forall {m n} (A : Matrix m n), A == A.
Proof. split; eauto. Qed.

Lemma mat_equiv_sym : forall {m n} (A B : Matrix m n), A == B -> B == A.
Proof.
  intros m n A B H i j Hi Hj. rewrite H; auto.
Qed.

Lemma mat_equiv_trans : forall {m n} (A B C : Matrix m n),
    A == B -> B == C -> A == C.
Proof.
  intros m n A B C H1 H2 i j Hi Hj. rewrite H1; [rewrite H2| |]; auto.
Qed.

Add Parametric Relation m n : (Matrix m n) (@mat_equiv m n)
  reflexivity proved by mat_equiv_refl
  symmetry proved by mat_equiv_sym
  transitivity proved by mat_equiv_trans
    as mat_equiv_rel.

(** Now we can use matrix equivalence to rewrite! *)

Lemma mat_equiv_trans2 : forall {m n} (A B C : Matrix m n),
    A == B -> A == C -> B == C.
Proof.
  intros m n A B C HAB HAC.
  rewrite <- HAB.
  apply HAC.
Qed.

Lemma mat_equiv_entries_eq : forall {m n}(A B:Matrix m n), A == B ->
  forall i j, (i<m)%N -> (j<n)%N -> A i j = B i j.
Proof. intros. apply H; auto. Qed.

Ltac meq := apply mat_equiv_entries_eq; try nomega.

(* ################################################################# *)
(** * Basic Matrices and Operations *)

Close Scope N_scope.
Open Scope C_scope.

(** Because we will use these so often, it is good to have them in matrix scope. *)
Notation "m =? n" := (N.eqb m n) (at level 70) : matrix_scope.
Notation "m <? n" := (N.ltb m n) (at level 70) : matrix_scope.
Notation "m <=? n" := (N.leb m n) (at level 70) : matrix_scope.

Open Scope matrix_scope.

Definition I (n : N) : Matrix n n := fun i j => if (i =? j)%N then 1 else 0.

Definition Zero (m n : N) : Matrix m n := fun _ _ => 0. 

Definition Mscale {m n : N} (c : C) (A : Matrix m n) : Matrix m n := 
  fun i j => c * A i j.

Definition Mplus {m n : N} (A B : Matrix m n) : Matrix m n :=
  fun i j => A i j + B i j.

Definition Mneg {m n : N} (A : Matrix m n) : Matrix m n :=
  fun i j => - A i j.

Definition Mminus {m n : N} (A B : Matrix m n) : Matrix m n :=
  Mplus A (Mneg B).

Notation ".- A" := (Mneg A) (at level 45) : matrix_scope.
Infix ".+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix ".-" := Mminus (at level 50, left associativity) : matrix_scope.
Infix ".*" := Mscale (at level 40, left associativity) : matrix_scope.

Lemma Mplus_assoc : forall {m n} (A B C : Matrix m n), (A .+ B) .+ C == A .+ (B .+ C).
Proof.
  intros m n A B C i j Hi Hj.
  unfold Mplus.
  lca.
Qed.

Lemma Mplus_comm : forall {m n} (A B : Matrix m n), A .+ B == B .+ A.
Proof.
  (* WORKED IN CLASS *)
  intros m n A B i j Hi Hj.
  unfold Mplus.
  lca.
Qed.
  
Lemma Mplus_0_l : forall {m n} (A : Matrix m n), Zero m n .+ A == A. 
Proof.
  (* WORKED IN CLASS *)
  intros m n A i j Hi Hj.
  unfold Zero, Mplus.
  lca.
Qed.
  
(* Let's try one without unfolding definitions. *)
Lemma Mplus_0_r : forall {m n} (A : Matrix m n), A .+ Zero m n == A. 
Proof.
  (* WORKED IN CLASS *)
  intros m n A.
  rewrite Mplus_comm.
  apply Mplus_0_l.
Qed.

Lemma Mplus_compat : forall {m n} (A B A' B' : Matrix m n),
    A == A' -> B == B' -> A .+ B == A' .+ B'.
Proof.
  (* WORKED IN CLASS *)
  intros m n A B A' B' HA HB.
  intros i j Hi Hj.
  unfold Mplus.
  rewrite HA by lia.
  rewrite HB by lia.
  reflexivity.
Qed.
    
Add Parametric Morphism m n : (@Mplus m n)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mplus_mor.
Proof.
  intros A A' HA B B' HB.
  apply Mplus_compat; easy.
Qed.

Add Parametric Morphism m n : (@Mneg m n)
  with signature mat_equiv ==> mat_equiv as Mneg_mor.
Proof. intros. intros i j Hi Hj. unfold Mneg; rewrite H; auto. Qed.

Add Parametric Morphism m n : (@Mminus m n)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mminus_mor.
Proof. intros. unfold Mminus. rewrite H; rewrite H0; easy. Qed.



(** Now let's return to that lemma... *)

Lemma Mplus3 : forall {m n} (A B C : Matrix m n), (B .+ A) .+ C == A .+ (B .+ C).
Proof.
  (* WORKED IN CLASS *)
  intros m n A B C.
  rewrite (Mplus_comm B A).
  apply Mplus_assoc.
Qed.

(** Mscale is similarly compatible with [==], but requires a slightly
    different lemma: *)

Lemma Mscale_compat : forall {m n} (c c' : C) (A A' : Matrix m n),
    c = c' -> A == A' -> c .* A == c' .* A'.
Proof.
  intros m n c c' A A' Hc HA.
  intros i j Hi Hj.
  unfold Mscale.
  rewrite Hc, HA; easy.
Qed.

Add Parametric Morphism m n : (@Mscale m n)
  with signature eq ==> mat_equiv ==> mat_equiv as Mscale_mor.
Proof.
  intros; apply Mscale_compat; easy.
Qed.

(** Let's move on to the more interesting matrix functions: *)

Definition trace {n : N} (A : Square n) : C := 
  Csum (fun x => A x x) n.

Definition Mmult {m n o : N} (A : Matrix m n) (B : Matrix n o) : Matrix m o := 
  fun x z => Csum (fun y => A x y * B y z) n.

Open Scope N_scope.

Definition kron {m n o p : N} (A : Matrix m n) (B : Matrix o p) : 
  Matrix (m*o) (n*p) :=
  fun x y => Cmult (A (x / o) (y / p)) (B (x mod o) (y mod p)).

Definition transpose {m n} (A : Matrix m n) : Matrix n m := 
  fun x y => A y x.

Definition adjoint {m n} (A : Matrix m n) : Matrix n m := 
  fun x y => (A y x)^*.

(** We can derive the dot product and its complex analogue, the 
    _inner product_, from matrix multiplication. *)

Definition dot {n : N} (A : Vector n) (B : Vector n) : C :=
  Mmult (transpose A) B 0 0.

Definition inner_product {n} (u v : Vector n) : C := 
  Mmult (adjoint u) (v) 0 0.

(** The _outer product_ produces a square matrix from two vectors. *)

Definition outer_product {n} (u v : Vector n) : Square n := 
  Mmult u (adjoint v).

Close Scope N_scope.

Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 41, left associativity) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope. 
Notation "A †" := (adjoint A) (at level 0) : matrix_scope. 
Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Notation "⟨ A , B ⟩" := (inner_product A B) : matrix_scope.

(* ================================================================= *)
(** ** Compatibility lemmas *)

Ltac nomega := zify; omega.

Lemma trace_compat : forall {n} (A A' : Square n),
    A == A' -> trace A = trace A'.
Proof.
  intros n A A' H.
  apply Csum_eq.
  intros x Hx.
  rewrite H. easy. 1,2:nomega.
Qed.

Add Parametric Morphism n : (@trace n)
  with signature mat_equiv ==> eq as trace_mor.
Proof. intros; apply trace_compat; easy. Qed.

Lemma Mmult_compat : forall {m n o} (A A' : Matrix m n) (B B' : Matrix n o),
    A == A' -> B == B' -> A × B == A' × B'.
Proof.
  intros m n o A A' B B' HA HB i j Hi Hj.
  unfold Mmult.
  apply Csum_eq; intros x Hx.
  rewrite HA, HB; try auto; nomega.
Qed.

Add Parametric Morphism m n o : (@Mmult m n o)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mmult_mor.
Proof. intros. apply Mmult_compat; easy. Qed.

Lemma kron_compat : forall {m n o p} (A A' : Matrix m n) (B B' : Matrix o p),
    A == A' -> B == B' -> A ⊗ B == A' ⊗ B'.
Proof.
  intros m n o p A A' B B' HA HB.
  intros i j Hi Hj.
  unfold kron.
  assert (Ho : o <> 0%N). intros F. rewrite F in *. lia.
  assert (Hp : p <> 0%N). intros F. rewrite F in *. lia.
  rewrite HA, HB. easy.
  - apply N.mod_upper_bound; easy.
  - apply N.mod_upper_bound; easy.
  - apply N.div_lt_upper_bound; lia.
  - apply N.div_lt_upper_bound; lia.
Qed.

Add Parametric Morphism m n o p : (@kron m n o p)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as kron_mor.
Proof. intros. apply kron_compat; easy. Qed.

Lemma transpose_compat : forall {m n} (A A' : Matrix m n),
    A == A' -> A⊤ == A'⊤.
Proof.
  intros m n A A' H.
  intros i j Hi Hj.
  unfold transpose.
  rewrite H; easy.
Qed.

Add Parametric Morphism m n : (@transpose m n)
  with signature mat_equiv ==> mat_equiv as transpose_mor.
Proof. intros. apply transpose_compat; easy. Qed.

Lemma adjoint_compat : forall {m n} (A A' : Matrix m n),
    A == A' -> A† == A'†.
Proof.
  intros m n A A' H.
  intros i j Hi Hj.
  unfold adjoint.
  rewrite H; easy.
Qed.

Add Parametric Morphism m n : (@adjoint m n)
  with signature mat_equiv ==> mat_equiv as adjoint_mor.
Proof. intros. apply adjoint_compat; easy. Qed.

Lemma innprod_compat : forall {n}(x x' y y' : Vector n),
  x == x' -> y == y' -> ⟨x,y⟩ = ⟨x',y'⟩.
Proof. intros. unfold inner_product. apply Mmult_compat; try auto.
apply adjoint_compat; auto. 1,2:apply N.lt_0_1.
Qed.

Add Parametric Morphism n : (@inner_product n)
  with signature mat_equiv ==> mat_equiv ==> eq as innprod_mor.
Proof. intros. apply innprod_compat; easy.
Qed.



(* ################################################################# *)
(** * Matrix Automation *)

(** A useful tactic for solving A == B for concrete A, B *)

Ltac solve_end :=
  match goal with
  | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.
                
Ltac by_cell := 
  intros i j Hi Hj;
  repeat (destruct i as [|i]; simpl; [|apply lt_S_n in Hi]; try solve_end); clear Hi;
  repeat (destruct j as [|j]; simpl; [|apply lt_S_n in Hj]; try solve_end); clear Hj.

Ltac lma := by_cell; lca.

(** Let's test it! *)                                                     
Lemma scale0_concrete : 0 .* I 10 == Zero _ _.
Proof. lma. Qed.


Ltac mintros := intros i j Hi Hj.


(* ################################################################# *)
(** * Matrix Properties *)

Theorem Mmult_assoc : forall {m n o p : N} (A : Matrix m n) (B : Matrix n o) 
  (C: Matrix o p), A × B × C == A × (B × C).
Proof.
  intros m n o p.
  unfold Mmult.
  N.induct n; intros.
  - simpl. intros i j Hi Hj.
    apply Csum_0. intros. lca.
  - intros i j Hi Hj. rewrite Csum_succ.
    rewrite <- H; eauto.
    rewrite Csum_mult_l. rewrite <- Csum_plus.
    apply Csum_eq; intros. rewrite Csum_succ. rewrite Cmult_plus_distr_r.
    rewrite Cmult_assoc. auto.
Qed.

Theorem Mmult_plus_distr_l : forall {m n p}(A: Matrix m n)(B C: Matrix n p),
  A × (B .+ C) == A×B .+ A×C.
Proof.
  intros. unfold Mmult, Mplus. intros i j Hi Hj.
  rewrite <- Csum_plus. apply Csum_eq; intros; field.
Qed.

Theorem Mmult_plus_distr_r : forall {m n p}(A B: Matrix m n)(C: Matrix n p),
  (A .+ B) × C  == A×C .+ B×C.
Proof.
  intros. unfold Mmult, Mplus. intros i j Hi Hj.
  rewrite <- Csum_plus. apply Csum_eq; intros; field.
Qed.

Lemma Mneg_mult_distr_l : forall {m n p}(A: Matrix m n)(B: Matrix n p),
  .- A×B == (.-A)×B.
Proof. intros. unfold Mneg, Mmult; mintros. rewrite Csum_neg.
apply Csum_eq; intros; lca.
Qed.

Lemma Mmult_neg_cancel : forall {m n p}(A: Matrix m n)(B: Matrix n p),
  (.-A)×(.-B) == A×B.
Proof. intros. unfold Mneg, Mmult; mintros. apply Csum_eq. intros; lca.
Qed.

Lemma Mmult_adjoint : forall {m n o : N} (A : Matrix m n) (B : Matrix n o),
      (A × B)† == B† × A†.
Proof.
  intros m n o A B i j Hi Hj.
  unfold Mmult, adjoint.
  rewrite Csum_conj_distr.
  apply Csum_eq; intros.
  rewrite Cconj_mult_distr.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma Mmult_1_l: forall (m n : N) (A : Matrix m n), 
  I m × A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  apply Csum_unique with i. nomega.
  unfold I. rewrite N.eqb_refl. lca.
  intros x Hx.
  unfold I.
  apply N.eqb_neq in Hx. rewrite Hx.
  lca.
Qed.

Lemma Mmult_1_r: forall (m n : N) (A : Matrix m n), 
  A × I n == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  eapply Csum_unique. apply Hj.
  unfold I. rewrite N.eqb_refl. lca.
  intros x Hx.
  unfold I.
  apply N.eqb_neq in Hx. rewrite N.eqb_sym. rewrite Hx.
  lca.
Qed.

Lemma adjoint_sum : forall {m n} (A B: Matrix m n), (A .+ B)† == A† .+ B†.
Proof. intros; mintros; lca. Qed.

Lemma adjoint_involutive : forall {m n} (A : Matrix m n), A†† == A.
Proof.
  (* WORKED IN CLASS *)
  intros m n A i j _ _.
  lca.
Qed.  
  
Lemma kron_adjoint : forall {m n o p} (A : Matrix m n) (B : Matrix o p),
  (A ⊗ B)† == A† ⊗ B†.
Proof. 
  (* WORKED IN CLASS *)
  intros m n o p A B.
  intros i j Hi Hj.
  unfold adjoint, kron. 
  rewrite Cconj_mult_distr.
  reflexivity.
Qed.

Lemma trace_mult : forall {m n}(A: Matrix m n)(B: Matrix n m),
  trace (A×B) = trace (B×A).
Proof.
  intros. unfold trace, Mmult. rewrite Csum_order.
  apply Csum_eq; intros; apply Csum_eq; intros; field.
Qed.

Lemma trace_plus : forall {n}(A B: Square n),
  trace (A .+ B) = trace A + trace B.
Proof. intros; unfold trace, Mplus; simpl. apply Csum_plus.
Qed.

Lemma trace_zero : forall {n}, trace (Zero n n) = 0.
Proof. unfold trace, Zero; intros. apply Csum_0; intros; field.
Qed.

Lemma trace_neg : forall {n}(A: Square n), - trace A = trace (.- A).
Proof. intros. unfold trace, Mneg. apply Csum_neg.
Qed.

Lemma Mmult_0_l : forall {m n p}(M: Matrix n p),
  (Zero m n) × M == Zero m p.
Proof. intros. unfold Zero, Mmult; by_cell. apply Csum_0; intros; field.
Qed.

Lemma Mmult_0_r : forall {m n p}(M: Matrix m n),
  M × (Zero n p) == Zero m p.
Proof. intros. unfold Zero, Mmult; by_cell. apply Csum_0; intros; field.
Qed.

Lemma Mscale_mult_comm : forall {m n p} c (A: Matrix m n)(B: Matrix n p),
  c .* (A×B) == A × (c.*B).
Proof. intros. unfold Mmult, Mscale; mintros. rewrite Csum_mult_l.
  apply Csum_eq; intros; field.
Qed.

Lemma innprod_distr_r : forall {n}(x y z: Vector n), ⟨x, y.+z⟩ = ⟨x, y⟩ + ⟨x, z⟩.
Proof. intros. unfold inner_product. rewrite Mmult_plus_distr_l. unfold Mplus. auto. 1,2:nomega.
Qed.

Lemma vectnorm_nonneg : forall {n}(v: Vector n), 0 <= ⟨v,v⟩.
Proof.
  intros. unfold inner_product, Mmult, adjoint; simpl.
  apply Csum_ge0. intros. split; [|split]. lca. lca. simpl. nra.
Qed.

Lemma Mminus_same : forall {m n}(A: Matrix m n), A .- A == Zero m n.
Proof. intros. lma. Qed.

Lemma Mneg_zero_zero : forall {m n}, .- Zero m n == Zero m n.
Proof. intros. lma. Qed.

Lemma innprod_zero : forall {n}(x: Vector n), ⟨x,x⟩ = 0 <-> x == Zero n 1.
Proof. unfold inner_product. split; intros.
- mintros. unfold Mmult in H. assert (j=0)%N by nomega; subst.
  epose proof (Csum_nonneg_0 _ _ _ H). specialize (H0 i Hi). simpl in H0.
  unfold adjoint in H0. unfold Zero; simpl. apply Cnorm2_0_0.
  apply RtoC_inj. rewrite <- Cconj_mult_norm2. rewrite Cmult_comm; auto.
- apply Csum_0. intros. specialize (H x0 0%N). rewrite H. apply Cmult_0_r.
  auto. nomega. Unshelve. intros. simpl. split. lca. split. lca. simpl. nra.
Qed.

(** Tensor Product facts *)

(*
Definition mat_equiv2 (m1 n1 m2 n2:N)(A B : N -> N -> C) :=
  m1 = m2 /\ n1 = n2 /\ @mat_equiv m1 m2 A B.

Definition mat_equiv3 {m1 n1 m2 n2}(A: Matrix m1 n1)(B: Matrix m2 n2) :=
  mat_equiv2 m1 n1 m2 n2 A B.

Infix "===" := mat_equiv3 (at level 80).
*)



(* idea: define the original mat_equiv on (N->N->C), and try to set
   so that implicit arguments are filled in when fed matrices  *)











Lemma kron_assoc : forall {m n o p q r} (A:Matrix m n)(B:Matrix o p)(C:Matrix q r),
  A ⊗ B ⊗ C == A ⊗ (B ⊗ C).
Proof. intros. unfold kron. intros i j Hi Hj.
repeat rewrite N.div_div. repeat rewrite (N.mul_comm o). repeat rewrite (N.mul_comm p).
do 4 try rewrite N.mod_mul_r at 1. rewrite (N.mul_comm q (_ mod _)); rewrite (N.mul_comm r (_ mod _)).
repeat rewrite N.div_add. do 2 replace (_ mod _ / _)%N with N0. do 2 rewrite N.add_0_l.
repeat rewrite N.mod_add. repeat rewrite N.mod_mod. apply Cmult_assoc.
5,7: symmetry; apply N.div_small_iff. 6,8: apply N.mod_upper_bound.
9: auto.
all: match goal with |[|- (?x <> 0)%N] => destruct x; try subst; try rewrite N.mul_0_r in *; try nomega
end.
Qed.


Lemma kron_mult : forall {m n p m' n' p'} (A:Matrix m n)(B:Matrix m' n')(C:Matrix n p)(D:Matrix n' p'),
  (A ⊗ B) × (C ⊗ D) == (A × C) ⊗ (B × D).
Proof.
intros. unfold kron, Mmult. mintros. rewrite Csum_convolution.
apply Csum_eq. intros. lca.
Qed.

Lemma kron_1 : forall {m n}, (I m) ⊗ (I n) == I(m*n).
Proof. intros. mintros. unfold kron, I; simpl.
destruct (N.eq_dec i j). subst. repeat rewrite N.eqb_refl. lca.
assert ((i =? j) = false) by (apply N.eqb_neq; auto). rewrite H.
assert (n<>0)%N by (intro; subst; nomega).
pose proof (N.div_mod i n H0). pose proof (N.div_mod j n H0).
destruct (N.eq_dec (i/n)(j/n)).
- replace (i mod n =? j mod n) with false. lca. symmetry; apply N.eqb_neq.
  intro. rewrite H3 in H1. rewrite e in H1. apply n0. rewrite H1. rewrite H2 at 3. auto.
- replace (i / n =? j / n) with false. lca. symmetry; apply N.eqb_neq. auto.
Qed.

Lemma kron_0_l : forall {m n o p}(A:Matrix o p), (Zero m n) ⊗ A == Zero _ _.
Proof. intros; unfold Zero, kron. mintros; lca.
Qed.

Lemma kron_0_r : forall {m n o p}(A:Matrix m n), A ⊗ (Zero o p) == Zero _ _.
Proof. intros; unfold Zero, kron. mintros; lca.
Qed.

Definition tensor {m k:N} (n:N) (f : N -> Matrix m k) :=
  N.peano_rect (fun p => Matrix (m^p)(k^p)) (I 1) (fun i M => M ⊗ (f i)) n.

(* Need to redo definition of tensor so that the type changes
over the recursion *)

(*
Add Parametric Morphism m k : (@tensor m k)
  with signature N.eq ==> mat_equiv ==> mat_equiv as tensor_mor.
Proof. intros. apply innprod_compat; easy.
Qed.*)

Lemma tensor_succ : forall {m k:N} n f,
  @tensor m k (N.succ n) f == (tensor n f) ⊗ (f n).
Proof. intros. unfold tensor. rewrite N.peano_rect_succ. reflexivity.
Qed.

Lemma tensor_succ_eq : forall {m k:N} n f,
  @tensor m k (N.succ n) f = (tensor n f) ⊗ (f n).
Proof. intros. unfold tensor. rewrite N.peano_rect_succ. reflexivity.
Qed.

(*
Theorem change_dim_eq : forall m n m' n' (A B:Matrix m n),
  m = m' -> n = n' -> @mat_equiv m n A B -> @mat_equiv m' n' A B.
Proof. intros. mintros; apply H1; nomega.
Qed.*)

Lemma tensor_mult : forall {m k o} n f g,
  (@tensor m k n f) × (@tensor k o n g) == tensor n (fun i => (f i)×(g i)).
Proof.
intros m k o n. N.induct n.
- intros. simpl. mintros. unfold Mmult, I. simpl. assert (i=0)%N by nomega; assert (j=0)%N by nomega. subst. simpl. lca.
- intros. repeat rewrite tensor_succ.
mintros.
rewrite N.pow_succ_r' in Hi,Hj. pose proof (kron_mult (tensor n f) (f n) (tensor n g) (g n)).
unfold Mmult in*. rewrite N.pow_succ_r'. rewrite N.mul_comm.
rewrite H0. unfold kron. rewrite H. auto. 
1,2:apply N.div_lt_upper_bound. 5,6:rewrite N.mul_comm. all:eauto.
all: (intros contra; subst; nomega).
Qed.


Lemma tensor_idx : forall n (f:N -> Square 2) i j (Hi:(i<n)%N) (Hj:(j<n)%N),
  (tensor n f) i j =
    Cprod (fun k => f k (N.b2n (N.testbit i (n-k-1))) (N.b2n (N.testbit j (n-k-1)))) n.
Proof.
intros n f. N.induct n; intros.
- nomega.
- rewrite tensor_succ. rewrite Cprod_succ. unfold kron at 1.

destruct (N.eq_dec n 0). assert (i=0/\j=0)%N by nomega. induction H0; subst.
simpl. unfold I. rewrite N.eqb_refl. rewrite N.mod_0_l. auto. nomega.

  rewrite H. apply f_equal2. apply Cprod_eq. intros.
  repeat rewrite N.sub_succ_l. repeat rewrite N.testbit_succ_r_div2.
  repeat rewrite N.div2_div. auto. 1,2,3,4:nomega.
  do 2 rewrite <- N.bit0_mod. replace (N.succ n - n - 1)%N with 0%N by nomega.
  auto. 1,2: apply N.div_lt_upper_bound. all:try nomega.
  all:pose proof (N.log2_le_lin i); pose proof (N.log2_le_lin j);
  apply N.log2_lt_cancel; rewrite N.log2_pow2; nomega.
Qed.

(* ********* *)


(** * Inverses *)

Definition mat_inverse {n} (A: Matrix n n) := {B | B × A == I n}.

Theorem Minv_nullsp0 : forall {n} (A: Matrix n n),
  mat_inverse A -> forall (x:Vector n), A × x == Zero n 1 -> x == Zero n 1.
Proof.
  intros. destruct X as [B HB]. rewrite <- Mmult_1_l at 1. rewrite <- HB.
  rewrite Mmult_assoc. rewrite H. unfold Mmult, Zero; by_cell; simpl; apply Csum_0; intros; lca.
Qed.




(** * Eigenstuff *)

(* need definition to include v != 0 *)
(*
Record NonZero n := mknonzerovect {
  nonzero :> Vector n;
  cond_nonzero : 0 < ⟨nonzero, nonzero⟩
}.

Definition eigenvalue {n}(A:Square n)(λ:C) := exists v:NonZero n, A×v == λ .* v.

Definition eigenvector {n}(A:Square n)(v:NonZero n) := exists λ:C, A×v == λ .* v.
*)

(** * Matrix Classes *)


Class Hermitian {n} (A: Square n) := {
  cond_hermitian : A == A†
}.
Add Parametric Morphism n : (@Hermitian n)
  with signature mat_equiv ==> iff as hermitian_mor.
Proof. repeat split; [rewrite <- H | rewrite H]; apply cond_hermitian. Qed.

Class Unitary {n} (A: Square n) := {
  cond_unitary : A† × A == I n
}.
Add Parametric Morphism n : (@Unitary n)
  with signature mat_equiv ==> iff as unitary_mor.
Proof. repeat split; [rewrite <- H | rewrite H]; apply cond_unitary. Qed.

Class PositiveSemidef {n} (A: Square n) := {
  psd_herm :> Hermitian A;
  cond_psd : forall (v:Vector n), 0 <= ⟨ v, A × v⟩
}.
Add Parametric Morphism n : (@PositiveSemidef n)
  with signature mat_equiv ==> iff as psd_mor.
Proof. split; split; intros; first [rewrite <- H | rewrite H]; 
first [typeclasses eauto|apply cond_psd]. Qed.

Class Projection {n} (A: Square n) := {
  cond_projection : A × A == A
}.
Add Parametric Morphism n : (@Projection n)
  with signature mat_equiv ==> iff as projection_mor.
Proof. repeat split; [rewrite <- H | rewrite H]; apply cond_projection. Qed.

Class OrthProjection {n} (A: Square n) := {
  orthproj_proj :> Projection A;
  orthproj_herm :> Hermitian A
}.
Add Parametric Morphism n : (@OrthProjection n)
  with signature mat_equiv ==> iff as orthproj_mor.
Proof. do 2 split; first [rewrite <- H | rewrite H]; typeclasses eauto. Qed.

Class Density {n} (A: Square n) := {
  density_psd :> PositiveSemidef A;
  cond_density : trace A = 1
}.
Add Parametric Morphism n : (@Density n)
  with signature mat_equiv ==> iff as density_mor.
Proof. do 2 split; first [rewrite <- H | rewrite H];
first [typeclasses eauto|apply cond_density]. Qed.

Class PartialDensityMatrix {n} (A: Square n) := {
  pdm_psd :> PositiveSemidef A;
  cond_pdm : 0 <= trace A <= 1
}.
Notation PDM := PartialDensityMatrix.
Add Parametric Morphism n : (@PartialDensityMatrix n)
  with signature mat_equiv ==> iff as pdm_mor.
Proof. do 2 split; first [rewrite <- H | rewrite H];
first [typeclasses eauto|apply cond_pdm]. Qed.

Class OrthProjPair {n} (A B: Square n) := {
  oppair_op1 :> OrthProjection A;
  oppair_op2 :> OrthProjection B;
  cond_oppair : A .+ B == I n
}.
Add Parametric Morphism n : (@OrthProjPair n)
  with signature mat_equiv ==> mat_equiv ==> iff as oppair_mor.
Proof. do 2 split; first [rewrite<-H|rewrite H|rewrite<-H0|rewrite H0];
try typeclasses eauto; [rewrite<-H0|rewrite H0]; apply cond_oppair. Qed.

(* Theorems on matrix classes *)
Typeclasses eauto := 5.


Lemma herm_diag_real : forall {n} (H:Square n) {Hherm: Hermitian H} (i:N),
  (i<n)%N -> (H i i) = (H i i)^*.
Proof. intros. apply cond_hermitian; eauto.
Qed.

Lemma herm_trace_real : forall {n} (H:Square n), Hermitian H ->
  trace H = (trace H)^*.
Proof. unfold trace; intros; simpl.
rewrite Csum_conj_distr. apply Csum_eq. apply herm_diag_real. auto.
Qed.

Instance unitary_adjoint_unitary : forall {n} U `{Unitary n U},
  Unitary U†.
Proof. Admitted.

Instance herm_conj_herm : forall {n m}(H:Square n)(M:Matrix m n)`{Hermitian _ H},
  Hermitian (M×H×M†).
Proof. intros. constructor. rewrite Mmult_assoc at 2. do 2 rewrite Mmult_adjoint.
rewrite adjoint_involutive. rewrite cond_hermitian at 1. reflexivity.
Qed.

Instance psd_conj_unitary_psd : forall {n}(A U:Square n)`{PositiveSemidef _ A}`{Unitary _ U},
  PositiveSemidef (U×A×U†).
Proof. intros. constructor; [constructor|]. apply herm_conj_herm. apply psd_herm. intros.
assert (v†×(U×A×U†×v) == (U†×v)†×(A×(U†×v))). do 2 rewrite Mmult_assoc at 1.
rewrite <- Mmult_assoc at 1. rewrite Mmult_adjoint. rewrite adjoint_involutive. easy.
unfold inner_product. rewrite H1; try auto. apply cond_psd. 1,2:nomega.
Qed.

Theorem conj_preserves_trace : forall {n} M U `{Unitary n U},
  trace (U×M×U†) = trace M.
Proof. intros. rewrite trace_mult. rewrite <- Mmult_assoc.
rewrite cond_unitary. rewrite Mmult_1_l. auto.
Qed.

Instance density_conj_unitary_density : forall {n}(rho U:Square n)`{Density _ rho}`{Unitary _ U},
  Density (U×rho×U†).
Proof. intros. split; try typeclasses eauto. rewrite conj_preserves_trace. apply cond_density. eauto.
Qed.

Instance pdm_conj_unitary_pdm : forall {n}(rho U:Square n)`{PDM rho}`{Unitary _ U},
  PDM (U×rho×U†).
Proof. intros. split; try typeclasses eauto. rewrite conj_preserves_trace. apply cond_pdm. eauto.
Qed.

Lemma orthproj_pairs_prod0 : forall {n}(P1 P2: Square n)`{OrthProjPair _ P1 P2},
  P1×P2 == Zero n n.
Proof.
  intros. assert (P1 == I n .- P2). unfold Mminus, Mplus, Mneg in *.
  intros i j Hi Hj. rewrite <- cond_oppair; [unfold Mplus; field|auto|auto].
  rewrite H0. unfold Mminus; rewrite Mmult_plus_distr_r.
  rewrite Mmult_1_l. intros i j Hi Hj; unfold Mmult, Mplus, Mneg, Zero.
  rewrite <- cond_projection. unfold Mmult. rewrite <- Csum_plus.
  apply Csum_0. intros; field. all: auto.
Qed.

Instance oppair_sym : forall {n} P1 P2 `{OrthProjPair n P1 P2},
  OrthProjPair P2 P1.
Proof. intros. split; try typeclasses eauto. rewrite Mplus_comm; apply cond_oppair.
Qed.

Lemma measure_output_preserves_trace : forall {n} (P1 P2 M: Square n) `{OrthProjPair n P1 P2},
  trace (P1×M×P1 .+ P2×M×P2) = trace M.
Proof.
  intros. symmetry. rewrite <- Mmult_1_l at 1. rewrite <- Mmult_1_r at 1.
  rewrite <- cond_oppair. rewrite Mmult_plus_distr_l. repeat rewrite Mmult_plus_distr_r.
  repeat rewrite trace_plus. rewrite (trace_mult (P2×_) P1). rewrite (trace_mult (P1×_) P2).
  do 2 rewrite <- Mmult_assoc. rewrite (orthproj_pairs_prod0 P1 P2).
  rewrite (orthproj_pairs_prod0 P2 P1). rewrite Mmult_0_l. rewrite trace_zero. field.
Qed.

Instance herm_sum_herm : forall {n:N} A B `{Hermitian n A} `{Hermitian n B},
  Hermitian (A .+ B).
Proof. intros. split. rewrite adjoint_sum. rewrite (@cond_hermitian _ A) at 1.
rewrite (@cond_hermitian _ B) at 1. easy. all:auto.
Qed.

Instance herm_neg_herm : forall {n:N} A `{Hermitian n A},
  Hermitian (.- A).
Proof. split. unfold Mneg, adjoint. mintros. rewrite Cconj_opp. rewrite cond_hermitian; auto.
Qed.

Instance herm_minus_herm : forall {n:N} A B `{Hermitian n A} `{Hermitian n B},
  Hermitian (A .- B).
Proof. intros. typeclasses eauto.
Qed.

Instance herm_bilinform_real_matform : forall {n} A (v: Vector n)`{Hermitian n A},
  Hermitian (v†×(A×v)).
Proof. intros. split. rewrite <- Mmult_assoc. rewrite <- (adjoint_involutive v) at 2 4.
apply cond_hermitian.
Qed.

Lemma herm_bilinform_real : forall {n} A (v: Vector n)`{Hermitian n A},
  ⟨v, A×v⟩  = ⟨v, A×v⟩^*.
Proof. intros. apply (@cond_hermitian _ _ (herm_bilinform_real_matform _ _)); nomega.
Qed.

Lemma herm_innprod : forall {n} A (v: Vector n)`{Hermitian n A},
   ⟨v, A×v⟩  = ⟨A×v, v⟩.
Proof. intros. unfold inner_product. meq. rewrite Mmult_adjoint.
rewrite <- cond_hermitian. symmetry. apply Mmult_assoc.
Qed.

Instance psd_sum_psd : forall {n} A B `{PositiveSemidef n A}`{PositiveSemidef n B},
  PositiveSemidef (A .+ B).
Proof. intros. split. typeclasses eauto 3. intro; simpl.
rewrite (innprod_compat _ _ _ _ (reflexivity v) (Mmult_plus_distr_r A B v)).
rewrite innprod_distr_r. repeat split; try lca. rewrite Cconj_plus_distr.
rewrite (herm_bilinform_real A) at 1. rewrite (herm_bilinform_real B v) at 1. auto.
apply psd_herm.
apply Rplus_le_le_0_compat.
assert (0 <= ⟨ v,A×v⟩).
  autounfold; apply cond_psd.
destruct H1. destruct H2. auto.
assert (0 <= ⟨ v,B×v⟩).
  autounfold; apply cond_psd.
destruct H1. destruct H2. auto.
Qed.

Instance herm_herm_herm : forall {n} A B `{Hermitian n A}`{Hermitian n B},
  Hermitian (B×A×B).
Proof.
  constructor. rewrite cond_hermitian at 2 4. apply herm_conj_herm; auto.
Qed.

Instance astara_herm : forall {m n}(A: Matrix m n), Hermitian (A†×A).
Proof. split. rewrite Mmult_adjoint. rewrite adjoint_involutive; easy.
Qed.

Lemma innprod_norm_ge0 : forall {n}(v: Vector n), 0 <= ⟨v,v⟩.
Proof. intros. repeat split; try lca; unfold inner_product.
apply astara_herm; nomega. unfold adjoint, Mmult; simpl.
generalize dependent v. N.induct n; intros. simpl. lra. rewrite Csum_succ. apply Rplus_le_le_0_compat. auto.
unfold C; simpl. nra.
Qed.

Instance astara_psd : forall {m n}(A: Matrix m n),
  PositiveSemidef (A†×A).
Proof. split. typeclasses eauto.
unfold inner_product. intros. assert (v†×(A†×A×v)==(A×v)†×(A×v)).
rewrite Mmult_assoc at 1. rewrite <- Mmult_assoc at 1.
rewrite Mmult_adjoint. easy. rewrite H; try nomega. apply innprod_norm_ge0.
Qed.

Instance orthproj_psd : forall {n} A `{OrthProjection n A}, PositiveSemidef A.
Proof. split. typeclasses eauto. intros. unfold inner_product. assert (v†×(A×v) == (A×v)†×(A×v)).
rewrite <- cond_projection at 1. rewrite cond_hermitian at 1.
rewrite Mmult_assoc at 1. rewrite <- Mmult_assoc at 1. rewrite Mmult_adjoint. easy.
rewrite H0; try nomega. apply innprod_norm_ge0.
Qed.

Instance psd_multlr_psd_herm : forall {n} A B `{PositiveSemidef n A}`{Hermitian n B},
  Hermitian (B×A×B).
Proof. split. do 2 rewrite Mmult_adjoint. rewrite <- cond_hermitian.
rewrite <- (@cond_hermitian _ A). apply Mmult_assoc. typeclasses eauto.
Qed.

Instance psd_multlr_psd_psd : forall {n} A B `{PositiveSemidef n A}`{Hermitian n B},
  PositiveSemidef (B×A×B).
Proof. split. typeclasses eauto.
unfold inner_product. intros. assert (v†×(B×A×B×v)==((B×v)†×(A×(B×v)))).
do 5 rewrite <- Mmult_assoc. rewrite cond_hermitian at 1. rewrite Mmult_adjoint; easy.
rewrite H1; try nomega. generalize (B×v). autounfold. apply cond_psd.
Qed.


Instance density_pdm : forall {n} A `{Density n A},
  PDM A.
Proof. intros. split. typeclasses eauto. rewrite cond_density.
repeat split; try lca; try nra. apply Rle_0_1.
Qed.




Instance I_herm : forall {n}, Hermitian (I n).
Proof. split. unfold I, adjoint; mintros.
rewrite N.eqb_sym; destruct (j =? i); lca.
Qed.

Instance I_psd : forall {n}, PositiveSemidef (I n).
Proof. split. typeclasses eauto. intros. erewrite innprod_compat.
apply (vectnorm_nonneg v). easy. apply Mmult_1_l.
Qed.

Instance I_unitary : forall {n}, Unitary (I n).
Proof. split. rewrite <- cond_hermitian. apply Mmult_1_l.
Qed.

Instance zero_herm : forall {n}, Hermitian (Zero n n).
Proof. split; unfold I, adjoint; intros; lma. Qed.

Instance zero_psd : forall {n}, PositiveSemidef (Zero n n).
Proof. split; try typeclasses eauto; intros. erewrite innprod_compat. unfold inner_product.
rewrite Mmult_0_r; try nomega. unfold Zero; simpl. repeat split; try lca; lra.
reflexivity. apply Mmult_0_l.
Qed.


Lemma trace_herm_herm_real : forall {n} A B `{Hermitian n A}`{Hermitian n B},
  trace (A×B) = (trace (A×B))^*.
Proof. intros. rewrite cond_hermitian at 1; rewrite (@cond_hermitian _ B) at 1 by auto;
rewrite <- Mmult_adjoint; rewrite trace_mult; unfold trace, adjoint;
rewrite Csum_conj_distr; auto.
Qed.

Instance orthproj_haspair : forall {n} A `{OrthProjection n A},
  OrthProjection (I n .- A).
Proof. split. split. unfold Mminus. rewrite Mmult_plus_distr_l.
do 2 rewrite Mmult_plus_distr_r. repeat rewrite Mmult_1_l. repeat rewrite Mmult_1_r.
rewrite Mplus_assoc. apply Mplus_compat. easy. rewrite Mmult_neg_cancel.
rewrite cond_projection. lma. typeclasses eauto.
Qed.


(** *********)

(* Loewner Order *)


Class loewner_le {n} (A B: Square n) :=
  cond_lle :> PositiveSemidef (B .- A).
Add Parametric Morphism n : (@loewner_le n)
  with signature mat_equiv ==> mat_equiv ==> iff as lle_mor.
Proof. do 2 split; intros; first [rewrite<-H; rewrite<-H0|rewrite H;rewrite H0];
first [typeclasses eauto|apply cond_psd]. Qed.

Infix "⊑" := loewner_le (at level 70) : matrix_scope.
Hint Unfold loewner_le.

Theorem lle_refl : forall {n}(A:Square n) ,
  A ⊑ A.
Proof. repeat autounfold; intros; simpl. split; [split|intros].
rewrite Mminus_same. apply cond_hermitian. rewrite Mminus_same.
rewrite Mmult_0_l. unfold inner_product; rewrite Mmult_0_r;
unfold Zero; try nomega. apply Cle_0_0.
Qed.

Theorem lle_trans : forall {n}(A B C: Square n),
  A ⊑ B -> B ⊑ C -> A ⊑ C.
Proof. repeat autounfold; intros; simpl in *.
assert (C.-A == (C.-B).+(B.-A)). unfold Mminus.
  rewrite Mplus_assoc. rewrite <- (Mplus_assoc (.-B)).
  rewrite (Mplus_comm (.-B)). setoid_rewrite Mminus_same.
  rewrite Mplus_0_l. easy.
rewrite H1. split. typeclasses eauto. intros. rewrite Mmult_plus_distr_r.
rewrite innprod_distr_r. apply Cplus_le_le_0_compat; apply cond_psd.
Qed.

Add Parametric Relation n : (Square n) (@loewner_le n)
      reflexivity proved by lle_refl
      transitivity proved by lle_trans
    as lle_rel.

Theorem lle_antisym : forall {n} A B `{PositiveSemidef n A}`{PositiveSemidef n B},
  A ⊑ B -> B ⊑ A -> A == B.
Proof. intros. mintros. autounfold in *. pose proof (@cond_psd _ _ H1). pose proof cond_psd. 
Abort.

Lemma lle_trace : forall {n}(A B:Square n),
  A ⊑ B <-> forall (rho:Square n), PDM rho -> trace (A×rho) <= trace (B×rho).
Proof.
  split; intros. assert (0 <= trace ((B .- A)×rho)).
    unfold trace; simpl. apply Csum_ge0; intros.
Admitted.
(* to prove this, need theorem that PDMs are lin combs of outer products *)
(* to prove that, need Spectral Theorem *)

Instance zero_lle_psd : forall {n} A `{PositiveSemidef n A},
  Zero n n ⊑ A.
Proof. intros. autounfold. unfold Mminus. rewrite Mneg_zero_zero. rewrite Mplus_0_r. auto.
Qed.





(** **************)

(* Predicates *)

Class Predicate {n} (A: Square n) := {
  predicate_psd :> PositiveSemidef A;
  cond_predicate : A ⊑ I n
}.
Add Parametric Morphism n : (@Predicate n)
  with signature mat_equiv ==> iff as predicate_mor.
Proof. do 2 split; first [rewrite <- H | rewrite H];
first [typeclasses eauto|apply cond_predicate]. Qed.






Instance orthproj_pred : forall {n} A `{OrthProjection n A},
  Predicate A.
Proof. split; autounfold; typeclasses eauto.
Qed.

Instance pdm_multlr_orthproj_pdm : forall {n} A P `{PDM A}`{OrthProjection n P},
  PDM (P×A×P).
Proof. split. typeclasses eauto. rewrite trace_mult. rewrite <- Mmult_assoc.
rewrite cond_projection. split. rewrite <- (@trace_zero n). erewrite <- Mmult_0_l.
apply lle_trace; typeclasses eauto. eapply Cle_trans. apply lle_trace.
apply cond_predicate. auto. rewrite Mmult_1_l. apply cond_pdm.
Qed.

Instance psd_prod_psd : forall {n} A B `{PositiveSemidef n A}`{PositiveSemidef n B}`{Hermitian n (A×B)},
  PositiveSemidef (A×B).
Proof.
intros. split; eauto. intro. assert (⟨v, B×v⟩ + ⟨B×v, A×B×v⟩ <= ⟨v, A×B×v⟩).
Abort.


(*
Theorem unitary_inverse_opp : forall {n} U,
  Unitary U -> U† × U == I n.
Proof. intros.
  by_cell. pose proof unitary. unfold I; destruct (i =? j) eqn:H1.
  pose proof (beq_nat_true _ _ H1). subst.
  unfold adjoint, Mmult in *; simpl in *. specialize (H0 j j); simpl in *.
*)

(*
Theorem hermitian_evals_real : forall {n} (M : Matrix n n),
  Hermitian M -> forall (x : Vector n), im ⟨ x, M × x ⟩ = 0.
Proof.
  intros. apply Creal_conj. unfold inner_product.
  assert (Hermitian (x† × (M × x))).
    unfold Hermitian. do 2 rewrite Mmult_adjoint.
    rewrite adjoint_involutive. rewrite <- Mmult_assoc.
    apply Mmult_compat. apply Mmult_compat.
      easy. apply hermitian. easy.
  rewrite H0 at 1; auto.
Qed.
*)

(*

Definition Lowner_le {n}(A B:Matrix n n) := 
  PositiveSemidef A /\ PositiveSemidef B /\ PositiveSemidef (B .- A).

(* change this notation to unicode *)
Infix "⊑" := Lowner_le (at level 70) : matrix_scope.

Theorem Lowner_density_trace : forall {n}(A B: Matrix n n),
  A =[ B <-> forall rho, PartialDensityMatrix rho -> trace (A×rho) <= trace (B×rho).
Proof.
  split; intros. split.

*)
Lemma Npow_succ : forall m n:N, (m ^ (N.succ n) = m^n * m)%N.
Proof. intros; rewrite N.pow_succ_r'; apply N.mul_comm.
Qed.

Lemma kron_prop_tensor_prop : forall (MatProp : forall k, Square k -> Prop),
  (forall m n (A:Square m)(B:Square n), MatProp _ A -> MatProp _ B -> MatProp _ (A⊗B))
    -> MatProp _ (I 1)
    -> forall n m (f:N -> Square m),
        (forall k, (k<n)%N -> MatProp _ (f k)) -> MatProp _ (tensor n f).
Proof. intros MatProp kron_prop HI n. N.induct n; intros.
- simpl. auto.
- rewrite tensor_succ_eq. rewrite Npow_succ. apply kron_prop.
apply H. intros. apply H0; nomega. apply H0; nomega.
Qed.

Instance kron_unitary : forall {m n} (A:Square m)(B:Square n),
  Unitary A -> Unitary B -> Unitary (A⊗B).
Proof. intros. split. rewrite kron_adjoint.
rewrite kron_mult. do 2 rewrite cond_unitary. apply kron_1.
Qed.

Instance tensor_unitary : forall n m (f:N -> Square m),
  (forall k, (k<n)%N -> Unitary (f k)) -> Unitary (tensor n f).
Proof. intros. apply kron_prop_tensor_prop; typeclasses eauto.
Qed.

Instance kron_herm : forall {m n} (A:Square m)(B:Square n),
  Hermitian A -> Hermitian B -> Hermitian (A⊗B).
Proof. intros. split. rewrite kron_adjoint.
rewrite cond_hermitian at 1; rewrite (@cond_hermitian _ B) at 1; [reflexivity|auto].
Qed.

Instance tensor_herm : forall n m (f:N -> Square m),
  (forall k, (k<n)%N -> Hermitian (f k)) -> Hermitian (tensor n f).
Proof. intros; apply kron_prop_tensor_prop; typeclasses eauto.
Qed.

Instance kron_proj : forall {m n} (A:Square m)(B:Square n),
  Projection A -> Projection B -> Projection (A⊗B).
Proof. intros. split. rewrite kron_mult.
repeat rewrite cond_projection. reflexivity.
Qed.

Instance tensor_proj : forall n m (f:N -> Square m),
  (forall k, (k<n)%N -> Unitary (f k)) -> Unitary (tensor n f).
Proof. apply kron_prop_tensor_prop; typeclasses eauto.
Qed.



Instance kron_psd : forall {m n} (A:Square m)(B:Square n),
  PositiveSemidef A -> PositiveSemidef B -> PositiveSemidef (A⊗B).
Proof. intros. split. typeclasses eauto.
intros. unfold inner_product.
Abort.


Definition psd_alt {n}(A:Square n) :=
  forall λ (v:Vector n),  ~(v == Zero _ _) -> A×v == λ .* v -> 0 <= λ.

Theorem psd_psd_alt : forall {n}(A:Square n), PositiveSemidef A <-> psd_alt A.
Proof. split; intros.
- admit.
- split. split. mintros. unfold adjoint. unfold psd_alt in H. Abort.


(*
 split; intros. split. lca. split. pose proof (cond_psd v).
rewrite H1 in H2. unfold inner_product in H2. rewrite <- Mscale_mult_comm in H2.
unfold Mscale in H2. inversion H2. inversion H4. rewrite Cconj_mult_distr in H5.
rewrite (@cond_hermitian _ _ _ 0%N 0%N) in H5 at 1. unfold adjoint in H5 at 1.
assert ((v†×v) 0%N 0%N <> 0). intro.
rewrite Mmult_adjoint in H5.*)










(*
Definition change_dim {m n}(A:Matrix m n) o p : Matrix o p := A.

Ltac mat_eq_dim2 o p :=
  match goal with
  |[|- @mat_equiv ?m ?n ?A ?B] =>
         unfold mat_equiv; replace m with o; replace n with p;
           fold (@mat_equiv o p A B)
  end.

Ltac mat_eq_dim p :=
  match goal with
  |[|- @mat_equiv ?m ?m ?A ?B] =>
         unfold mat_equiv; replace m with p;
           fold (@mat_equiv p p (change_dim A p p) (change_dim B p p))
  end.

Theorem mat_eq_stuff : forall m1 n1 m2 n2 (A B: N -> N -> C),
  m1 = m2 -> n1 = n2 -> @mat_equiv m1 n1 A B -> @mat_equiv m2 n2 A B.
Proof. unfold mat_equiv. intros. apply H1; nomega.
Qed.
*)
  

  
(* Thu Aug 1 13:45:52 EDT 2019 *)
