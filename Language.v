Require Export NamelessUTLC.Functor.

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

Fixpoint eqt (t1 t2: term) : bool :=
  match t1, t2 with
  | var n1, var n2 => n1 == n2
  | abs t1, abs t2 => eqt t1 t2
  | app fn1 arg1, app fn2 arg2 => eqt fn1 fn2 && eqt arg1 arg2
  | _, _ => false
  end.

Theorem eqtP : Equality.axiom eqt.
Proof. move=> t1 t2. apply: introP.
  - elim: t1 t2 => //=.
    + move=> n. case=> // ?. by move/eqP.
    + move=> ? IH. case=> // ?. by move/IH.
    + move=> ? IHf ? IHa. case=> // ? ?. by move/andP=> [/(IHf _)-> /(IHa _)->].
  - elim: t1 t2 => //=.
    + move=> n. case=> // ?. by move/eqP.
    + move=> ? IH. case=> // ?. by move/IH.
    + move=> ? IHf ? IHa. case=> // ? ?. move/nandP. by case=> [/IHf | /IHa].
Qed.

Definition term_eqMixin := EqMixin eqtP.
Canonical term_eqType := Eval hnf in EqType term term_eqMixin.

Definition bound (t: term) : nat :=
  @term_rec (fun _ => nat)
            (fun n => n.+1)
            (fun _ => predn)
            (fun _ n _ m => maxn n m)
            t.

Inductive bounded (n: nat) : term -> Prop :=
| BoundedVar k (lt: k < n) : bounded n k
| BoundedAbs t (t_bounded: bounded n.+1 t) : bounded n [fun t]
| BoundedApp t1 (t1_bounded: bounded n t1) t2 (t2_bounded: bounded n t2) : bounded n (t1 @ t2).

Hint Constructors bounded.

Lemma invert_bounded n t (H: bounded n t)
  : match t return Prop with
    | var k => k < n
    | abs t => bounded n.+1 t
    | app fn arg => bounded n fn /\ bounded n arg
    end.
Proof. case: t H => *; match goal with
                 | [ H: bounded _ _ |- _ ] => by inversion H
                 end. Qed.

Lemma boundedS : forall t n, bounded n t -> bounded n.+1 t.
Proof. elim; move=> *; match goal with
                 | [H: bounded _ _ |- _] => move: H; by invert
                 end.
Qed.

Hint Resolve boundedS.

Lemma bounded_leq : forall t n, bounded n t -> forall m, n <= m -> bounded m t.
Proof. elim.
  - move=> ? ? /invert_bounded-? ? ?. constructor. by apply: leq_trans; eauto.
  - move=> ? IH ? /invert_bounded-? ? ?. constructor. by apply: IH; eauto.
  - move=> ? IHf ? IHa ? /invert_bounded-[? ?] ? ?. constructor.
    + by apply: IHf; eauto.
    + by apply: IHa; eauto.
Qed.

Hint Resolve bounded_leq.

Lemma maxn_leq_andb n m p : maxn n m <= p = (n <= p) && (m <= p).
Proof. case n_leq_m: (n <= m); move: (n_leq_m).
  * move/maxn_idPl. rewrite maxnC => ->. case m_leq_p: (m <= p).
    -- by move: (leq_trans n_leq_m m_leq_p).
    -- by rewrite andbF.
  * move/negbT. rewrite -ltnNge. move/ltnW/maxn_idPr. rewrite maxnC=> ->.
    case n_leq_p: (n <= p) => //.
    move/negbT: n_leq_m n_leq_p. rewrite -ltnNge.
    move/ltnW=> m_leq_n n_leq_p. by move: (leq_trans m_leq_n n_leq_p).
Qed.

Theorem boundP : forall t n, reflect (forall m, n <= m -> bounded m t) (bound t <= n).
Proof. elim=> /=.
  - move=> n1 n2. apply: introP.
    + constructor. by apply: leq_trans; eauto.
    + rewrite -leqNgt => H. move/(_ n2 (leqnn n2))/invert_bounded.
      rewrite ltn_neqAle. move/andP=> [neq H']. move/andP/anti_leq: (conj H H').
      by move/eqP: neq.
  - move=> t IH n.
    have leq_sub1_add1: forall n m, (n.-1 <= m) = (n <= m.+1) by elim.
    rewrite {}leq_sub1_add1. apply: introP.
    + move=> Hbound m Hm.
      constructor. apply: IH.
      * exact: Hbound.
      * by rewrite ltnS.
    + move/(elimN (IH n.+1))=> {IH} contra. move/(_ n (leqnn _))/invert_bounded => H.
      apply: contra => m lt. by apply: bounded_leq; eauto.
  - move=> f IHf a IHa n.
    rewrite maxn_leq_andb.
    apply: introP.
    + move/andP=> [bf_leq ba_leq] m leq. move/(fun x => leq_trans x leq): bf_leq => ?.
      move/(fun x => leq_trans x leq): ba_leq => {leq} ?.
        by constructor; [apply: IHf | apply: IHa]; eauto.
    + move/nandP=> [/IHf-nbf | /IHa-nba] /(_ n (leqnn _))/invert_bounded-[? ?];
                    [apply: nbf | apply: nba] => ? ?; by apply: bounded_leq; eauto.
Qed.

Lemma boundEqP : forall t n, bound t == n -> forall m, n <= m -> bounded m t.
Proof. move=> t n. rewrite eqn_leq. move/andP=> [H _]. by move/boundP: H. Qed.

Definition shift_over (d: nat) : term -> nat -> term :=
  @term_rec (fun _ => nat -> term)
            (fun n c => if n < c then n else n + d)
            (fun _ rec c => [fun rec c.+1])
            (fun _ rec_f _ rec_a c => rec_f c @ rec_a c).

Definition shift (d: nat) : term -> term := shift_over d ^~ 0.

Lemma bound_shift_over {n t} : bounded n t -> forall {c d}, bounded (n + d) (shift_over d t c).
Proof. elim=> //= {n t}.
  move=> ? k ? c *. constructor. case: (k < c).
  - by apply: ltn_addr.
  - by rewrite ltn_add2r.
Qed.

Theorem bound_shift {n t d} : bounded n t -> bounded (n + d) (shift d t).
Proof. move=> *. by apply: bound_shift_over. Qed.

Definition substitute (substitution: term) (variable: nat) (t: term) : term :=
  @term_rec (fun _ => nat -> term -> term)
           (fun n v s => if n == v then s else n)
           (fun _ rec v s => [fun rec v.+1 (shift 1 s)])
           (fun _ rec_fn _ rec_arg v s => rec_fn v s @ rec_arg v s)
           t variable substitution.

Theorem bound_substitute {n t}
  : bounded n t -> forall s, bounded n s -> forall v, bounded n (substitute s v t).
Proof. elim=> //= {n t}.
  - move=> ? k ? ? ? v. by case: (k == v).
  - move=> ? ? ? IH ? bs ?. constructor.
    move/bound_shift: bs. move/(_ 1). rewrite addn1. by move/IH.
Qed.