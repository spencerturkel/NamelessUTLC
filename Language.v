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

Definition bound (t: term) : option nat :=
  @term_rec (fun _ => option nat)
            (fun n => Some n.+1)
            (fun _ n => Some n.-1)
            (fun _ n _ m => if n && (n == m) then n else None)
            t.

Definition shift (d: nat) (t: term) : term :=
  @term_rec (fun _ => nat -> term)
            (fun n c => if n < c then n else n + d)
            (fun _ rec n => [fun rec n.+1])
            (fun _ rec_f _ rec_a n => rec_f n @ rec_a n)
            t 0.

Definition substitute (substitution: term) (variable: nat) (t: term) : term :=
  @term_rec (fun _ => nat -> term -> term)
           (fun n v s => if n == v then s else n)
           (fun _ rec v s => [fun rec v.+1 (shift 1 s)])
           (fun _ rec_fn _ rec_arg v s => rec_fn v s @ rec_arg v s)
           t variable substitution.
