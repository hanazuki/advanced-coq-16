From mathcomp Require Import all_ssreflect.

Section Kosaraju.

  Variable T: finType.
  Implicit Types s: {set T}.
  Implicit Types l: seq T.
  Implicit Types A B C: pred T.
  Implicit Types x y z: T.

  Section Lib.

    Lemma disjoint_setU s1 s2 A: [disjoint s1 :|: s2 & A] = [disjoint s1 & A] && [disjoint s2 & A].
      apply/pred0P/andP.
      - move => H.
        split; apply/pred0P => x /=; apply/andP => [[H0 H1]];
        move: H => /(_ x) /= /andP; apply;
        split => //;
        rewrite in_setU;
        apply/orP; by [left | right].
      - move => [/pred0P D1 /pred0P D2] x /=.
        rewrite in_setU.
        move: D1 => /(_ x) /=.
        move: D2 => /(_ x) /=.
        by case: (x \in A); case: (x \in s1); case: (x \in s2).
    Qed.

    Lemma disjoint_setUr s1 s2 A: [disjoint A & s1 :|: s2] = [disjoint A & s1] && [disjoint A & s2].
      rewrite disjoint_sym disjoint_setU.
      by congr andb; rewrite disjoint_sym.
    Qed.

    Lemma disjoint_catr l1 l2 A: [disjoint A & l1 ++ l2] = [disjoint A & l1] && [disjoint A & l2].
      rewrite disjoint_sym disjoint_cat.
      by congr andb; rewrite disjoint_sym.
    Qed.

    Lemma disjoint_set1 x A: [disjoint [set x] & A] = (x \notin A).
      apply/pred0P/negP.
      - move => /(_ x) /= /andP H H0.
        apply: H.
        by rewrite in_set1.
      - move => H y /=.
        rewrite in_set1.
        by apply/andP => [[/eqP H0]]; subst.
    Qed.

    Lemma disjoint_setU1 x s A: [disjoint x |: s & A] = (x \notin A) && [disjoint s & A].
      apply/pred0P/andP.
      - move => H; split.
        -- apply/negP => H0.
           move: H => /(_ x) /= /andP; apply.
           split => //; exact: setU11.
        -- apply/pred0P => y /=.
           apply/andP => [[H0 H1]].
           move: H => /(_ y) /= /andP; apply.
           split => //; exact: setU1r.
      - move => [/negP H0 /pred0P H1] y /=.
        rewrite in_setU1.
        apply/andP => [[/orP H2 H3]].
        move: H1 => /(_ y) /= /andP; apply.
        by split; case: H2 => // /eqP H; subst.
    Qed.

    Lemma disjoint_setU1r x s A: [disjoint A & x |: s] = (x \notin A) && [disjoint A & s].
      rewrite disjoint_sym disjoint_setU1.
      by congr andb; rewrite disjoint_sym.
    Qed.

    Lemma disjoint_consr x l A: [disjoint A & x :: l] = (x \notin A) && [disjoint A & l].
      rewrite disjoint_sym disjoint_cons.
      by congr andb; rewrite disjoint_sym.
    Qed.

    Lemma in_subset A B x: A \subset B -> x \in A -> x \in B.
      rewrite subsetE => /pred0P /(_ x)/= /andP.
      rewrite /(x \notin _).
      by case: (x \in A); case: (x \in B); tauto.
    Qed.

    Lemma disjoint_transr {A B C}: B \subset C -> [disjoint A & C] -> [disjoint A & B].
      move => H.
      rewrite disjoint_sym => D.
      rewrite disjoint_sym.
      exact: (disjoint_trans H).
    Qed.
  End Lib.

  Section Stack.
    Section Rconnect.
      Variable r: rel T.

      Definition rconnect s := connect [rel x y | (r x y) && (y \notin s)].
      Local Notation "x -[ s ]-> y" := (rconnect s x y) (at level 10, format "x  -[ s ]->  y").
      Local Notation "x -[]-> y" := (rconnect set0 x y) (at level 10, format "x  -[]->  y").

      Lemma seq_in_nth {p: seq T} {x: T}: x \in p -> exists n: nat, n < size p /\ forall x0, nth x0 p n = x.
        elim: p => /= [|y p IH].
        - by rewrite in_nil.
        - rewrite in_cons => /orP; case.
          -- by move/eqP => ?; subst; exists 0.
          -- move => H; move: IH => /(_ H) {H} [n H]; by exists (n.+1).
      Qed.

      Lemma fuga (p: seq T) (s: {set T}) n: n < size p -> [disjoint p & s] -> forall x0, nth x0 p n \notin s.
        move => H0 /pred0P H1 x0; apply/negP => H2.
        move: H1 => /(_ (nth x0 p n)) => /= /andP; apply; split => //.
        apply/nthP.
        by exists n.
      Qed.

      Lemma path_relE s x p: path [rel x y | (r x y) && (y \notin s)] x p = path r x p && [disjoint p & s].
        apply/pathP/andP.
        - move => H.
          split.
          -- apply/pathP => i H1.
             move: H => /(_ i H1) {H1} /= /andP.
             instantiate (1:= x).
             instantiate (2:= x).
             by tauto.
          -- apply/pred0P => y /=.
             apply/andP => [[H2 H3]].
             move: (seq_in_nth H2) => [i [H4 /(_ x) H5]].
             move: H => /(_ i H4) {H4} /= /andP [H6 /negP H7].
             by subst.
        - move => [/pathP H1 H2] i H3 /=.
          move: H1 => /(_ x i H3) => H1.
          apply/andP; intuition.
          exact: fuga.
      Qed.

      Lemma rconnectP s x y: reflect (exists2 p, path r x p & ((y = last x p) /\ [disjoint p & s])) (x -[s]-> y).
        apply: (iffP connectP).
        - move => [p H0].
          move: H0; rewrite path_relE => /andP.
          exists p; by tauto.
        - move => [p H0] [H1 H2].
          exists p => //.
          by rewrite path_relE; apply/andP.
      Qed.

      Lemma rconnect_set0: rconnect set0 =2 connect r.
        move => x y.
        apply/rconnectP/connectP.
        - move => [p H0] [H1 H2].
          exists p => //.
        - move => [p H0].
          exists p => //; split => //.
          apply/pred0P => z /=.
          rewrite in_set0.
          by apply/andP; intuition.
      Qed.

      Lemma rconnect_ref s : reflexive (rconnect s).
        move => x.
        apply/rconnectP.
        exists [::] => //; split => //.
        exact: disjoint0.
      Qed.

      Lemma rconnect1 s x y : y \notin s -> r x y -> x -[s]-> y.
        move => H0 H1.
        apply/rconnectP.
        exists [:: y] => /=.
        - by apply/andP.
        - rewrite disjoint_cons.
          split => //; apply/andP; split => //.
          exact: disjoint0.
      Qed.

      Lemma hoge {i n m}: i < n + m -> i < n \/ exists2 j, i = j + n & j < m.
        move => Hnm.
        case ltnP => Hn; intuition; right.
        exists (i - n).
        by rewrite subnK.
        by rewrite -(ltn_add2l n) subnKC.
      Qed.

      Lemma rconnect_trans s : transitive (rconnect s).
        move => y x z /rconnectP [p Hp] [-> Dps] /rconnectP [q Hq] [-> Dqs].
        apply/rconnectP.
        exists (p ++ q).
        - by rewrite cat_path; apply/andP.
        - split.
          -- by rewrite last_cat.
          -- by rewrite disjoint_cat; apply/andP.
      Qed.

      Lemma rconnect_subset (s1 s2 : {set T}) x y: {subset s1 <= s2} ->  x -[s2]-> y -> x -[s1]-> y.
        move => /subsetP S /rconnectP [p H0 [H1 H2]]; apply/rconnectP.
        exists p => //; split => //.
        exact: (disjoint_transr S).
      Qed.

      Lemma rconnect_setU {s1 s2 x y}: [disjoint [set z | x -[s1]-> z && z -[s1]-> y] & s2] -> x -[s1]-> y ->  x -[s2 :|: s1]-> y.
        move => H0 /rconnectP [p H1 [H2 H3]]; apply/rconnectP; subst.
        exists p => //; split => //.
        apply/pred0P => a /=; rewrite in_setU; apply/andP => [[H4 /orP H5]].
        move: (H4) => /splitPr => /= H7.
        inversion H7 as [p0 p1 H6]; symmetry in H6. (*** todo *)
        case: H5 => H5.
        - move: H0 => /pred0P /(_ a) /= /andP; apply; intuition.
          apply/setIdP.
          split; apply/rconnectP.
          -- move: H6; rewrite -cat1s catA => ?; subst.
             move: H1; rewrite (cat_path r x _ _) => /andP[H1 H2].
             exists (p0 ++ [:: a]) => //=.
             split.
             --- by rewrite last_cat.
             --- by move: H3; rewrite disjoint_cat => /andP[].
          -- subst.
             exists p1.
             --- by move: H1; rewrite cat_path => /= /andP[_ /andP[]].
             --- split.
                 ---- by rewrite last_cat last_cons.
                 ---- move: H3; rewrite disjoint_cat => /andP [_].
                      by rewrite disjoint_cons => /andP; intuition.
        - by move: H3 => /pred0P /(_ a) /= /andP; apply.
      Qed.

    Lemma rconnect_setU1r s x y z: ~~ z -[s]-> y ->  x -[s]-> y -> x -[z |: s]-> y.
      move => /negP H0.
      suff: [disjoint [set w | x -[s]->w && w-[s]-> y] & [set z] ] by exact: rconnect_setU.
      rewrite disjoint_sym disjoint_set1.
      by apply/negP => /setIdP [_ ?]; apply: H0.
    Qed.

    Lemma rconnect_setU1l s x y z: ~~ (x -[s]-> z) ->  x -[s]-> y -> x -[z |: s]-> y.
      move => /negP H0.
      suff: [disjoint [set w | x -[s]->w && w-[s]-> y] & [set z] ] by exact: rconnect_setU.
      rewrite disjoint_sym disjoint_set1.
      by apply/negP => /setIdP [? _]; apply: H0.
    Qed.

    Lemma rconnect_id_setU1 s x y : x -[x |: s]-> y = x -[s]-> y.
      apply/rconnectP/rconnectP.
      - move => [p H0 [H1]].
        rewrite disjoint_setU1r => /andP.
        exists p => //; split => //; intuition.
      - move => [p].
        move Hn: (size p) => n; move: Hn.
        move: p.
        elim/Wf_nat.lt_wf_ind: n => [n IH].
        move => p /esym H0 [H1] [H2 H3]; subst.
        case H4: (x \in p).
        -- move: H4 => /splitPr H4.
           inversion H4 as [p0 p1 H5]; symmetry in H5; subst.
           apply: IH.
           instantiate (1:=size p1).
           by apply/ltP; rewrite size_cat /= ltn_addl.
           by instantiate (1:=p1).
           by move: H1; rewrite cat_path /= => /andP[_] /andP[].
           split; first by rewrite last_cat last_cons.
           by move: H3; rewrite disjoint_cat disjoint_cons => /andP[_] /andP[].
        -- exists p => //; split => //.
           rewrite disjoint_setU1r.
           apply/andP; split => //.
           by apply/negP; move: H4 => /negP.
    Qed.
