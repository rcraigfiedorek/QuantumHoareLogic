

Require Export QuantumHoareLogic.Matrix.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Setoid.
Require Import NArith.

Open Scope matrix_scope.

Typeclasses eauto := 10.

Section QNLcomDef.
Context {n:N}.

(* Quantum programming language w/ no loops on n qubits initialized to zero *)
(* state space has dimension 2^n *)
Inductive QNLcom :=
  | QNLSkip : QNLcom
  | QNLTransform (U: Square(2^n))`{Unitary _ U} : QNLcom
  | QNLSeq : QNLcom -> QNLcom -> QNLcom
  | QNLMeasure (P1 P2: Square(2^n)) `{OrthProjPair _ P1 P2} :
     QNLcom -> QNLcom -> QNLcom.

Fixpoint eval (com : QNLcom) (rho: Square(2^n)) : Square(2^n) :=
  match com with
  | QNLSkip => rho
  | QNLTransform U => U×rho×U†
  | QNLSeq c1 c2 => eval c2 (eval c1 rho)
  | QNLMeasure P1 P2 c1 c2 =>
      (eval c1 (P1×rho×P1)) .+ (eval c2 (P2×rho×P2))
  end.


Theorem eval_compat : forall com rho rho', 
  rho == rho' -> eval com rho == eval com rho'.
Proof. induction com; intros; simpl; try easy.
rewrite H0; easy. apply IHcom2. apply IHcom1. auto.
rewrite IHcom1; [rewrite IHcom2; [|rewrite H0] | rewrite H0]; easy.
Qed.

Add Parametric Morphism com : (eval com)
  with signature mat_equiv ==> mat_equiv as eval_mor.
Proof.
apply eval_compat.
Qed.

Instance eval_psd : forall com rho `{PositiveSemidef _ rho},
  PositiveSemidef (eval com rho).
Proof.
  induction com; simpl; try (intros; typeclasses eauto).
Qed.

Theorem eval_preserves_trace : forall com rho,
  trace (eval com rho) = trace rho.
Proof.
  induction com; simpl; intros.
    auto.
    apply conj_preserves_trace; auto.
    rewrite IHcom2; apply IHcom1.
    rewrite trace_plus; rewrite IHcom1; rewrite IHcom2.
      rewrite <- trace_plus. apply measure_output_preserves_trace; auto.
Qed.

Global Instance eval_density : forall com rho `{Density _ rho},
  Density (eval com rho).
Proof.
  induction com; try (intros; typeclasses eauto).
  split. typeclasses eauto. rewrite eval_preserves_trace. apply cond_density.
Qed.

Global Instance eval_pdm : forall com rho `{PDM rho},
  PDM (eval com rho).
Proof.
  induction com; try (intros; typeclasses eauto).
  split. typeclasses eauto. rewrite eval_preserves_trace. apply cond_pdm.
Qed.

End QNLcomDef.


Bind Scope qnl_scope with QNLcom.
Delimit Scope qnl_scope with qnl.
Notation "'SKIP'" := QNLSkip : qnl_scope.
Notation "'TRANSFORM' U" := (QNLTransform U) (at level 60) : qnl_scope.
Notation "c1 ;; c2" :=
  (QNLSeq c1 c2) (at level 80, right associativity) : qnl_scope.
Notation "'MEASURE' P1 : c1 ;; P2 : c2 ;; 'ENDMEASURE'" :=
  (QNLMeasure P1 P2 c1 c2) (at level 90, P1 at level 50, P2 at level 50, c1 at level 50, c2 at level 50, right associativity) : qnl_scope.
Open Scope qnl_scope.

(* ******** *)



(*
  split; [|split]; try (
      rewrite cond_hermitian at 2; rewrite (cond_hermitian _ rho) at 2;
      rewrite trace_mult; rewrite <- Mmult_adjoint; unfold trace;
      unfold adjoint; rewrite Csum_conj_distr; apply Csum_eq;
      intros; rewrite Cconj_involutive; auto
    ).
    apply Rge_le. apply Rminus_ge. unfold Rminus. rewrite Cre_opp.
      rewrite Cre_plus. rewrite trace_neg. rewrite <- trace_plus.
      rewrite Mneg_mult_distr_l. rewrite <- Mmult_plus_distr_r.
    pose (M := B .+ .- A). replace (B .+ .- A) with M by auto.
    unfold trace, Mmult; simpl. apply Csum_ge0.
*)

Section CorrectnessFormulas.
Context {n:N}.

Definition Correct (com:QNLcom)(P Q: Square (2^n))`{Predicate _ P}`{Predicate _ Q} : Prop :=
  forall (rho: Square(2^n)) `{PDM rho},
    trace (P × rho) <= trace (Q × (eval com rho)).

Notation "'{{' P '}}' com '{{' Q '}}'" := (Correct com P Q) (at level 20) : qnl_scope.
Hint Unfold Correct.


Theorem skip_rule : forall P `{Predicate _ P},
  {{ P }} SKIP {{ P }}.
Proof. autounfold; intros; simpl; split; [|split];
try apply trace_herm_herm_real; try typeclasses eauto. apply (Rle_refl).
Qed.

Theorem seq_rule : forall P Q R c1 c2 `{Predicate _ P}`{Predicate _ Q}`{Predicate _ R},
  {{P}} c1 {{Q}} -> {{Q}} c2 {{R}} -> {{P}} c1 ;; c2 {{R}}.
Proof. autounfold; intros; simpl. eapply Cle_trans.
apply H2. apply PDM0. apply H3. typeclasses eauto.
Qed.

Theorem transform_rule : forall P U `{Predicate _ P}`{Unitary _ U}`{Predicate _ (U†×P×U)},
  ({{U†×P×U}} TRANSFORM U {{P}}).
Proof. autounfold; simpl; intros. repeat rewrite <- Mmult_assoc. rewrite <- (trace_mult U†).
repeat rewrite <- Mmult_assoc. apply lle_trace. reflexivity. typeclasses eauto.
Qed.

Instance transform_rule_pred : forall {n} P U `{Predicate (2^n) P}`{Unitary (2^n) U},
  Predicate (U†×P×U).
Proof. split. rewrite <- (adjoint_involutive U) at 2. typeclasses eauto.
apply lle_trace. intros. rewrite Mmult_1_l. repeat rewrite Mmult_assoc.
rewrite trace_mult. repeat rewrite Mmult_assoc. rewrite <- (Mmult_assoc U).
rewrite <- (conj_preserves_trace rho U). rewrite <- (Mmult_1_l _ _ (U×_×_)) at 2.
apply lle_trace. apply cond_predicate. typeclasses eauto.
Qed.

Theorem measurement_rule : forall P1 P2 Q M1 M2 c1 c2 `{Predicate _ P1}`{Predicate _ P2}`{Predicate _ Q}`{OrthProjPair _ M1 M2}`{Predicate _ (M1×P1×M1 .+ M2×P2×M2)},
  {{P1}} c1 {{Q}} -> {{P2}} c2 {{Q}} ->
    {{ M1×P1×M1 .+ M2×P2×M2 }} MEASURE M1: c1;; M2: c2;; ENDMEASURE {{ Q }}.
Proof. intros; autounfold; simpl; intros. rewrite Mmult_plus_distr_r.
rewrite Mmult_plus_distr_l. do 2 rewrite trace_plus. repeat rewrite Mmult_assoc.
rewrite trace_mult. rewrite (trace_mult M2). rewrite Mmult_assoc. rewrite (Mmult_assoc P2).
apply Cplus_le_compat; [apply H4|apply H5]; typeclasses eauto.
Qed.

Instance measurement_rule_pred : forall {n} P1 P2 M1 M2 `{Predicate (2^n) P1}`{Predicate (2^n) P2}`{OrthProjPair (2^n) M1 M2},
  Predicate (M1×P1×M1 .+ M2×P2×M2).
Proof. intros. split. typeclasses eauto. apply lle_trace. intros.
rewrite Mmult_1_l. rewrite Mmult_plus_distr_r. rewrite trace_plus.
repeat rewrite Mmult_assoc. rewrite trace_mult.
rewrite (trace_mult M2). rewrite Mmult_assoc. rewrite (Mmult_assoc P2).
rewrite <- (measure_output_preserves_trace M1 M2 rho). rewrite trace_plus.
eapply Cplus_le_compat; (rewrite <- (Mmult_1_l _ _ (_×rho×_)) at 2;
apply lle_trace; [apply cond_predicate | typeclasses eauto]).
Qed.

Theorem weakening_rule_l : forall P P' Q com `{Predicate _ P}`{Predicate _ P'}`{Predicate _ Q},
  P ⊑ P' -> {{P'}} com {{Q}} -> {{P}} com {{Q}}.
Proof. intros; unfold Correct; intros.
eapply Cle_trans. apply lle_trace. apply H2. auto. apply H3. auto.
Qed.

Theorem weakening_rule_r : forall P Q Q' com `{Predicate _ P}`{Predicate _ Q}`{Predicate _ Q'},
  Q' ⊑ Q -> {{P}} com {{Q'}} -> {{P}} com {{Q}}.
Proof. intros; unfold Correct; intros.
eapply Cle_trans. apply H3; auto. apply lle_trace. apply H2. typeclasses eauto.
Qed.

(* weakest precondition *)
Fixpoint WP (com:QNLcom) (P: Square n) : Square(2^n) :=
  match com with
  | QNLSkip => P
  | QNLTransform U => U†×P×U
  | QNLSeq c1 c2 => WP c1 (WP c2 P)
  | QNLMeasure M1 M2 c1 c2 =>
      M1 × (WP c1 P) × M1 .+ M2 × (WP c2 P) × M2
  end.

Instance wp_pred_pred : forall com P `{Predicate (2^n) P},
  Predicate (WP com P).
Proof. induction com; simpl; intros; typeclasses eauto.
Qed.

Theorem wp_correct : forall com P `{Predicate (2^n) P},
  {{WP com P}} com {{P}}.
Proof.
  induction com; simpl; intros.
    - apply (@skip_rule _ H).
    - apply transform_rule.
    - eapply (seq_rule _ (WP com2 P)). eapply IHcom1. eapply IHcom2.
    - eapply measurement_rule. eapply IHcom1. eapply IHcom2.
Qed.

Theorem wp_trace : forall com P rho `{Predicate (2^n) P}`{PDM rho},
  trace ((WP com P) × rho) = trace (P × (eval com rho)).
Proof.
  induction com; simpl; intros.
    - auto.
    - repeat rewrite Mmult_assoc. rewrite (trace_mult U†).
      repeat rewrite Mmult_assoc. auto.
    - rewrite IHcom1; [apply IHcom2| | ]; typeclasses eauto.
    - rewrite Mmult_plus_distr_l. rewrite Mmult_plus_distr_r.
      do 2 rewrite trace_plus. apply Cplus_compat;
      repeat rewrite Mmult_assoc; rewrite trace_mult; rewrite Mmult_assoc;
      [apply IHcom1|apply IHcom2]; typeclasses eauto.
Qed.

Theorem wp_weakest : forall com P Q `{Predicate _ P}`{Predicate _ Q},
  {{Q}} com {{P}} <-> Q ⊑ WP com P.
Proof. split. intros. apply lle_trace. intros. rewrite wp_trace. apply H1. 1,2,3:typeclasses eauto.
intros. eapply (weakening_rule_l _ (WP com P)). auto. apply wp_correct.
Qed.

End CorrectnessFormulas.

























