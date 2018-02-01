From mathcomp Require Import all_ssreflect.

Implicit Type p q r: bool.
Implicit Type m n a b c: nat.

Lemma orbC p q: p || q = q || p.
  by case: p; case q. Qed.

Lemma Pirce p q: ((p ==> q) ==> p) ==> p.
  by case: p; case q. Qed.

Lemma bool_gimmics1 a: a != a.-1 -> a != 0.
  by elim: a. Qed.

Lemma find_me p q: ~~p = q -> p (+) q.
  by case: p; case q. Qed.

Lemma view_gimmics1 p a b: p -> (p ==> (a == b.*2)) -> a./2 = b.
  case p => //= _ => /eqP ->; exact: doubleK.
Qed.

Lemma view_gimmics2 p q r: ~~p && (r == q) -> q ==> (p || r).
  by case: p; case q; case r.
Qed.

Lemma iterSr A n (f: A -> A) x: iter n.+1 f x = iter n f (f x).
  elim: n => //= _ -> //.
Qed.

Lemma iter_predn m n: iter n predn m = m - n.
  elim: n => //=.
    by rewrite subn0.
    by move=> n ->; rewrite subnS.
Qed.

Lemma ltn_nqqAle m n: (m < n) = (m != n) && (m <= n).
    by rewrite ltnNge leq_eqVlt negb_or -leqNgt eq_sym.
Qed.

Lemma maxn_idPl m n: reflect (maxn m n = m) (m >= n).
  rewrite -subn_eq0 -(eqn_add2l m) addn0 maxnE.
  apply: eqP.
Qed.