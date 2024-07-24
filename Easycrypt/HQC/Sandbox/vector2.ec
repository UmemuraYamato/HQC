  axiom addvA (v1 v2 v3 : vector):
    (v1 + v2) + v3 = v1 + (v2 + v3).

  axiom addvC (v1 v2 : vector):
    v1 + v2 = v2 + v1.

  axiom add0v (v : vector):
    zerov + v = v.

  axiom addNv (v : vector):
    v + -v = zerov.

  (** Ring multiplication *)
  const onev: vector.
  op ( * ): vector -> vector -> vector.

  axiom mulvA (v1 v2 v3 : vector):
    (v1 * v2) * v3 = v1 * (v2 * v3).

  axiom mul1v (v : vector):
    onev * v = v.

    (* lemmas *)

  lemma addv0 (v : vector):
    v + zerov = v.
  proof strict.
  by rewrite addvC add0v.
  qed.

  lemma addvN (v : vector):
    -v + v = zerov.
  proof strict.
  by rewrite addvC addNv.
  qed.
(**
lemma mulvN (v : vector):
    one =


  lemma addIv (v v1 v2 : vector):
    (v1 + v = v2 + v) =>
    v1 = v2.
  proof strict.
   move=> v1_v2.
   by rewrite -addv0 -(addv0 v2) -(addNv v) -2!addvA -v1_v2.
  qed.

  axiom mul1m (m : matrix):
    onem ^* m = m.

 (** lemma trmx1m (m : matrix):
    m * (trmx m) = onem.
    proof.
    rewrite -mul1m.**)

  lemma mulvM (v : vector) (m1 m2 : matrix):
      (v ^* m1 = v ^* m2) =>
      m1 = m2.
    proof strict.
      move => m1_m2.
   rewrite -mul1m -(mul1m m2).

lemma addMv (v1 v2 v3 : vector) (m1 m2 m3 : matrix):
    (v1 ^* m1 + m3 *^ v2 + v3 = v1 ^* m2 + m3 *^ v2 + v3) =>
    m1 = m2.
  proof strict.
  move => m1_m2.
    rewrite -mul1m -(mul1m m2).


m{2} ^* g{1} + (H pk{2}.`2)%top *^ r2L + eL =
m{2} ^* g{2} + (H pk{2}.`2)%top *^ r2L + eL

**)
