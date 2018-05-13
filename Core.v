From mathcomp.ssreflect
     Require Export
     eqtype
     seq
     ssrbool
     ssrfun
     ssrnat
     ssreflect
.
Require Export Coq.Strings.String.
From CoqUtils Require Export string.

Global Set Implicit Arguments.
Global Unset Strict Implicit.
Global Unset Printing Implicit Defensive.
Global Set Bullet Behavior "Strict Subproofs".
Global Open Scope SEQ.
Global Open Scope string.

Ltac decompose_context :=
  match goal with
  | [ H: _ |- _ ] => progress (decompose record H); clear H
  | [ H: _ |- _ ] => progress (decompose sum H); clear H
  end.

Ltac done := intuition; hnf; intros;
            solve
              [ do ![solve [intuition | apply: sym_equal; intuition
                            | congruence
                            | econstructor; eauto
                            ]
                    | discriminate | contradiction
                    | constructor | progress (autorewrite with done_rw_db)
                    | decompose_context
                    | subst]
              | case not_locked_false_eq_true; assumption
              | match goal with H : ~ _ |- _ => solve [case H; intuition] end].

Ltac invert := let H := fresh in move=> H; inversion H; subst; clear H.