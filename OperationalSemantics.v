Require Export NamelessUTLC.Language.

Fixpoint unshift (t: term) :=
  match t return term with
  | var n => n.-1
  | abs t => [fun unshift t]
  | app fn arg => unshift fn @ unshift arg
  end.

Theorem unshift_bounded {n t} : bounded n t -> bounded n (unshift t).
Proof. elim=> //=. move=> {n t} ? k lt. constructor. by case: k lt. Qed.

Fixpoint reduce (t: term) : seq term :=
  match t with
  | var n => [::]
  | abs t => map abs (reduce t)
  | app fn arg =>
    (if fn is abs body
     then [:: unshift (substitute (shift 1 arg) 0 body)]
     else [::]) ++ map (app ^~ arg) (reduce fn) ++ map (app fn) (reduce arg)
  end.

Fixpoint normal_step (t: term) : option term :=
  match t with
  | var n => None
  | abs t => fmap abs (normal_step t)
  | app (abs body) arg => Some (unshift (substitute (shift 1 arg) 0 body))
  | app fn arg => fmap (app ^~ arg) (normal_step fn)
  end.

Fixpoint cbn_step (t: term) : option term :=
  match t with
  | var n => None
  | abs t => None
  | app (abs body) arg => Some (unshift (substitute (shift 1 arg) 0 body))
  | app fn arg => fmap (app ^~ arg) (cbn_step fn)
  end.

Fixpoint cbv_step (t: term) : option term :=
  match t with
  | var n => None
  | abs t => None
  | app [fun body] [fun argbody] =>
    Some (unshift (substitute (shift 1 [fun argbody]) 0 body))
  | app fn arg => fmap (app ^~ arg) (cbv_step fn)
  end.

Lemma option_fmap_Some {A B f} {mx: option A} {y: B}
  : fmap f mx = Some y -> {x | mx = Some x /\ f x = y}.
Proof. case: mx => //= ?. by case. Qed.

Theorem reduce_contains_cbv : forall t t', cbv_step t = Some t' -> t' \in reduce t.
Proof. elim=> //= fn IHfn arg IHarg t.
  have H: match fn with
           | [ fun body] =>
             match arg with
             | [ fun argbody] => Some (unshift (substitute (shift 1 [ fun argbody]) 0 body))
             | _ => fmap (app^~ arg) (cbv_step fn)
             end
           | _ => fmap (app^~ arg) (cbv_step fn)
          end = Some t ->
          (exists body, fn = [fun body] /\
                   (exists argbody, arg = [fun argbody] /\
                                unshift (substitute (shift 1 [ fun argbody]) 0 body) = t))
          \/ (exists fn', cbv_step fn = Some fn' /\ fn' @ arg = t).
  {
    case: fn {IHfn} => //.
    - move=> ?. case: arg {IHarg} => //. move=> ?. case=> //.
    - move=> ? ? /option_fmap_Some-?. by right.
  }
  move/H=> {H}. case.
  - move=> [? [-> [? [-> ->]]]] /=. by rewrite in_cons eq_refl.
  - move=> [fn' [/IHfn-IH <-]] /= {IHfn IHarg}. rewrite mem_cat.
    apply/orP. right. rewrite mem_cat. apply/orP. left.
    by apply: map_f.
Qed.