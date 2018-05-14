Require Export NamelessUTLC.Language.

Fixpoint unshift (t: term) :=
  match t return term with
  | var n => n.-1
  | abs t => [fun unshift t]
  | app fn arg => unshift fn @ unshift arg
  end.

Theorem unshift_bounded {n t} : bounded n t -> bounded n (unshift t).
Proof. elim=> //=. constructor. by case: k lt. Qed.

Fixpoint step (t: term) : option term :=
  match t with
  | var n => None
  | abs t => None
  | app (abs t1) (abs t2) => Some (unshift (substitute (shift 1 t2) 0 t1))
  | app (abs t1) arg => fmap (app (abs t1)) (step arg)
  | app fn arg => fmap (app ^~ arg) (step fn)
  end.