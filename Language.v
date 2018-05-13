Require Export NamelessUTLC.Core.

Inductive term : Set := var (n: nat) :> term | abs (t: term) | app (fn: term) (arg: term).

Hint Constructors term.

Bind Scope term_scope with term.
Delimit Scope term_scope with term.
Notation "[ 'fun' e ]" := (abs e)
  (at level 0) : term_scope.
Notation "fn @ arg" :=
  (app fn arg)
    (at level 50, arg at next level, left associativity) : term_scope.
Global Open Scope term_scope.

Fixpoint bound (t: term) : option nat :=
  match t with
  | var n => Some n.+1
  | abs t => Some (bound t).-1
  | app fn arg => match bound fn with
                 | Some b => if Some b == bound arg then Some b else None
                 | None => None
                 end
  end.

Definition shift (d: nat) : term -> term :=
  (fix go (c: nat) (t: term) :=
     match t return term with
     | var n => if n < c then n else n + d
     | abs t => [fun go c.+1 t]
     | app fn arg => go c fn @ go c arg
     end) 0.

Goal shift 2 [fun [fun 1 @ (0 @ 2)]] = [fun [fun 1 @ (0 @ 4)]]. reflexivity. Qed.
Goal shift 2 [fun 0 @ 1 @ (0 @ 1 @ 2)] = [fun 0 @ 3 @ (0 @ 3 @ 4)]. reflexivity. Qed.

Inductive CAS : term -> nat -> term -> term -> Prop :=
| CASVarEq s v : CAS s v v s
| CASVarNotEq s v {t} (neq: t <> v) : CAS s v t t
| CASAbs {s v t t'} (cas: CAS (shift 1 s) v.+1 t t') : CAS s v [fun t] [fun t']
| CASApp {s v fn1 fn2 arg1 arg2} (cas1: CAS s v fn1 fn2) (cas2: CAS s v arg1 arg2)
  : CAS s v (fn1 @ arg1) (fn2 @ arg2).

Hint Constructors CAS.

Definition substitute (substitution: term) (variable: nat) (t: term) : term :=
  @term_rec (fun _ => nat -> term -> term)
           (fun n v s => if n == v then s else n)
           (fun _ rec v s => [fun rec v.+1 (shift 1 s)])
           (fun _ rec_fn _ rec_arg v s => rec_fn v s @ rec_arg v s)
           t variable substitution.

Ltac invert_cas := match goal with
                  | [ H: CAS _ _ (?P _) _ |- _ ] => move: H; invert
                  end.

Theorem substitute_cas : forall t s v t', CAS s v t t' <-> substitute s v t = t'.
Proof. elim=> //=.
  - move=> n ? v. case eq: (n == v); move/eqP: eq;
    [move=> -> ? | move=> ? ?]; split=> //; by invert.
  - move=> ? IH ? ? ?. split.
    + invert=> /=. move: cas. by rewrite IH.
    + move=> <-. constructor. by rewrite IH.
  - move=> f IHf a IHa s v t. split.
    + invert. move: cas1 cas2. by rewrite IHf IHa.
    + move=> <-. constructor.
      * by rewrite IHf.
      * by rewrite IHa.
Qed.
