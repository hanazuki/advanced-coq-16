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

    Lemma disjoint_predsetC A s: [disjoint A & s] = [disjoint s & A].
      by apply/pred0P/pred0P => H x /=; apply/andP => H0;
      move: H => /(_ x) /= /andP; apply; tauto.
    Qed.

    Lemma disjoint_setUr s1 s2 A: [disjoint A & s1 :|: s2] = [disjoint A & s1] && [disjoint A & s2].
      rewrite !disjoint_predsetC.
      exact: disjoint_setU.
    Qed.

    Lemma disjoint_catr l1 l2 A: [disjoint A & l1 ++ l2] = [disjoint A & l1] && [disjoint A & l2].
      apply/pred0P/andP.
      - move => H; split; apply/pred0P => x /=;
        apply/andP => [[H0 H1]]; move: H => /(_ x) /= /andP; apply;
        split => //; rewrite mem_cat; apply/orP; tauto.
      - move => [/pred0P D1 /pred0P D2] x /=.
        rewrite mem_cat andb_orr.
        move: D1 => /(_ x) /= /andP H1.
        move: D2 => /(_ x) /= /andP H2.
        by apply/orP; case; move/andP.
    Qed.

    Lemma disjoint_set1 x A: [disjoint [set x] & A] = (x \notin A).
      apply/pred0P/negP.
      - move => /(_ x) /= /andP H H0.
        apply: H.
        by rewrite in_set1.
      - move => H y /=.
        rewrite in_set1.
        by apply/andP => [[/eqP *]]; subst.
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
      rewrite !disjoint_predsetC.
      exact: disjoint_setU1.
    Qed.

    Lemma disjoint_consr x l A: [disjoint A & x :: l] = (x \notin A) && [disjoint A & l].
      apply/pred0P/andP.
      - move => H; split.
        -- apply/negP => H0.
           move: H => /(_ x) /= /andP; apply.
           split => //; exact: mem_head.
        -- apply/pred0P; move => y /=.
           apply/andP => [[H0 H1]].
           move: H => /(_ y) /= /andP; apply.
           split => //; exact: mem_behead.
      - move => [/negP H0 /pred0P H1] y /=.
        rewrite in_cons.
        apply/andP => [[H2 /orP H3]].
        move: H1 => /(_ y) /= /andP; apply.
        by split; case: H3 => // /eqP H; subst.
    Qed.

    Lemma in_subset A B x: A \subset B -> x \in A -> x \in B.
      rewrite subsetE => /pred0P /(_ x)/= /andP.
      rewrite /(x \notin _).
      by case: (x \in A); case: (x \in B); tauto.
    Qed.

    Lemma disjoint_transr A B C: B \subset C -> [disjoint A & C] -> [disjoint A & B].
      move => H /pred0P D.
      apply/pred0P; move => x /=.
      apply/andP => [[H0 H1]].
      move: D => /(_ x) /= /andP; apply.
      split => //.
      exact: (in_subset B).
    Qed.
  End Lib.

End Kosaraju.
