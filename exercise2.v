From mathcomp Require Import all_ssreflect.

Lemma cat_take_drop T n (s: seq T): take n s ++ drop n s = s.
  elim: s n => // a l IH [|n] //=.
  by rewrite IH.
Qed.

Lemma size_take T n (s: seq T): size (take n s) = if n < size s then n else size s.
  elim: s n => // a l IH [|n] //=.
  by rewrite IH ltnS; elim: (n < size l).
Qed.

Lemma takel_cat T n (s1 s2: seq T): n <= size s1 -> take n (s1 ++ s2) = take n s1.
  elim: s1 n.
  - by move=> /= n; rewrite leqn0 => /eqP ->; apply: take0.
  - by move=> a l IH [|n] //= H; rewrite IH.
Qed.

Lemma size_rot T n (s: seq T): size (rot n s) = size s.
  by rewrite /rot -[s in RHS](cat_take_drop _ n) !size_cat addnC.
Qed.

Lemma has_filter (T: eqType) a (s: seq T): has a s = (filter a s != [::]).
  by elim: s => //= x s ->; case: ifP.
Qed.

Lemma filter_all T a (s: seq T): all a (filter a s).
  by elim: s => //= x s IH; case: ifP => //= ->.
Qed.

Lemma all_filterP T a (s: seq T): reflect (filter a s = s) (all a s).
  apply: (iffP idP).
  - elim: s => //= x s IH.
    case: (a x) => //= H.
    by rewrite IH.
  - move=> <-; exact: filter_all.
Qed.

Lemma mem_cat (T: eqType) (x: T) s1 s2: (x \in s1 ++ s2) = (x \in s1) || (x \in s2).
  rewrite !/(_ \in _).
  elim: s1 s2 => //= y.
  by case: eqP.
Qed.

Lemma allP (T: eqType) (a: pred T) (s: seq T): reflect (forall x, x \in s -> a x) (all a s).
  apply: (iffP idP); elim: s => //= x s.
  - move=> IH /andP [Ax As] y.
    rewrite in_cons => /orP [/eqP ->|H] //.
    exact: IH.
  - move => H0 H1.
    apply/andP; split.
    -- apply: H1.
       exact: mem_head.
    -- apply: H0 => y Hys.
       apply: H1.
       exact: mem_behead.
Qed.
