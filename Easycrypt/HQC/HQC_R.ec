(* -------------------------------------------------------------------- *)
require import AllCore List Distr Perms.
require (*--*) Subtype Monoid Ring Subtype Bigalg StdOrder StdBigop.

import StdOrder.IntOrder StdBigop.Bigreal.

(* -------------------------------------------------------------------- *)
clone import Ring.ComRing as ZR.

(* -------------------------------------------------------------------- *)
clone import Bigalg.BigComRing as Big with theory CR <- ZR.

type R = t.

import BAdd.

(* -------------------------------------------------------------------- *)
op size : { int | 0 <= size } as ge0_size.

hint exact : ge0_size.

require import AllCore FSet List SmtMap CHoareTactic StdOrder.
require (*--*) BitWord Distr DInterval.
(*---*) import RealOrder RField StdBigop.Bigint BIA.
require (*--*) ROM  Matrix Ring Group ZModP PKE_CPA RingCloning.

clone RingCloning as RC.
import RC RC.Ring RC.RingT RC.CRing RC.CRingT RC.BRing RC.BRingT.

clone Matrix as Mt.
import Mt Mt.Vector Mt.Matrix.

(** Construction: a Matrix **)
type vector = Mt.vector.
type matrix = Mt.Matrix.matrix.

op dvector = Mt.Matrix.dvector.

op [lossless uniform full] duni_R : R distr.
op [lossless] dshort_R : R distr.
op duni = dvector duni_R.
op dshort = dvector dshort_R.

op H:vector -> matrix.

const g : matrix.

pred is_lossless_R (duni_R : R distr) = weight duni_R = 1%r.

lemma duniR_ll: is_lossless duni_R.
    proof. smt. qed.

lemma duni_ll: is_lossless duni.
    proof. smt. qed.

lemma dshort_ll: is_lossless dshort.
    proof. smt. qed.

(** Construction: a PKE **)
type pkey = vector * vector.
type skey = vector * vector.
type ptxt = vector.
type ctxt = vector * vector.

clone import PKE_CPA as PKE with
  type pkey <- pkey,
  type skey <- skey,
  type ptxt <- ptxt,
  type ctxt <- ctxt.


(** Concrete Construction: HQC_PKE **)
module HQC_PKE : Scheme = {
  proc kg():pkey *skey = {
  var x,y,h,h',s,pk,sk;

    x  <$ dshort;              (* ZModP p=2 -> F_2 *)
    y  <$ dshort;
    h  <$ duni;
    h' <- (H h);               (* h -> H making for QC *)
    s <- x + h' *^ y;
    pk <- (h, s);
    sk <- (x, y);

    return (pk,sk);
  }

  proc enc(pk:pkey, m:ptxt):ctxt = {
      var e,r1,r2,u,v,h,s,h',s',c;

    (h, s) <- pk;
    e  <$ dshort;
    r1 <$ dshort;
    r2 <$ dshort;
    h' <- (H h);
    s' <- (H s);

    u <- r1 + h' *^ r2;
    v <- m ^* g + s' *^ r2 + e;

    c <- (u, v);

    return c;
  }

  proc dec(sk:skey, c:ctxt):ptxt option = {
      var u,v,x,y,u';
    (u, v) <- c;
    (x, y) <- sk;
     u' <- (H u);

    return Some (v + ((-u' *^ y)));

  }
}.


(** Security Problem **)
module type Adversary = {
  proc choose(pk:pkey) : ptxt * ptxt
  proc guess(pk:pkey, c:ctxt) : bool
}.

module type Adv_T = {
  proc guess(h:vector, s:vector,  c:ctxt) : bool
}.

(**
module II_DQCSD_P(Adv : Adv_T) = {

  proc main(b : bool) : bool = {
    var r1, r2, k, k', u0, u1, p, p', e, v0, v1, b';

    r1 <$ dshort;
    r2 <$ dshort;
    h  <$ dshort;
    h' <- (H h);
    u0 <- r1 + h' *^ r2;
    u1 <$ duni;

    p <$ dshort;
    p' <- (H p);
    e <$ duni;
    v0 <- p' *^ r2 + e;
    v1 <$ duni;

    b' <@ Adv.guess(h, s, if b then (u1,v1) else (u0,v0));
    return b';
   }

 }.
    **)

module II_DQCSD_P(Adv : Adv_T) = {

  proc main(b : bool) : bool = {
    var r1, r2, h, h', u0, u1, s, s', e', v0, v1, b';

    r1 <$ dshort;
    r2 <$ dshort;
    h  <$ duni;
    h' <- (H h);
    u0 <- h' *^ r2 + r1;
    u1 <$ duni;

    s <$ duni;
    s' <- (H s);
    e' <$ dshort;
    v0 <- s' *^ r2 + e';
    v1 <$ duni;

    b' <@ Adv.guess(h, s, if b then (u1,v1) else (u0,v0));
    return b';
   }

}.

module B1(A : Adversary) : Adv_T = {

  proc kg(h: vector, s: vector) : pkey * skey = {
       return ((h, s), witness);
  }

  proc guess(h: vector, s: vector, c:ctxt) : bool = {
      var pk, sk, m0, m1, b, b';

    (pk,sk)  <@ kg(h, s);
    (m0, m1) <@ A.choose(pk);
    b        <$ {0,1};
    c        <@ HQC_PKE.enc(pk, m0);
    b'       <@ A.guess(pk, c);

    return b' = b;
  }
}.


(** Reduction: from a PKE adversary, construct a Syndrome adversary **)

section Security.
  declare module A <: Adversary.
  declare axiom Ac_ll: islossless A.choose.
  declare axiom Ag_ll: islossless A.guess.

  local module G1(A:Adversary) = {
    proc main () : bool = {
    var pk: pkey;
    var sk: skey;
    var c: ctxt;
    var m0, m1: ptxt;
    var b: bool;

        (pk, sk) <@ HQC_PKE.kg();
        (m0, m1) <@ A.choose(pk);
        c        <@ HQC_PKE.enc(pk, m0);
        b        <@ A.guess(pk, c);
        return b;

    }
  }.


  local module G2(A:Adversary) = {
    proc main () : bool = {
     var pk: pkey;
     var sk: skey;
     var c: ctxt;
     var m0, m1: ptxt;
     var b: bool;
     var h, s;

        (pk, sk) <@ HQC_PKE.kg();
        (h, s)   <- pk;
        s        <$ duni;
        pk       <- (h, s);
        sk       <- (zerov, zerov);
        (m0, m1) <@ A.choose(pk);
        c        <@ HQC_PKE.enc(pk, m0);
        b        <@ A.guess(pk, c);
        return b;
    }
  }.

(** Lemma 1 **)
lemma hop1_left &m:
  Pr[G1(A).main() @ &m : res] = Pr[II_DQCSD_P(B1(A)).main(false) @ &m : res].
proof.
byequiv=> //.
  proc. inline. wp.
  call(_:true); wp; do 3! rnd; wp => /=; rnd{2}.
  call(_:true). wp => /=; rnd{2}; wp; rnd{2}; wp; do 2! rnd{2}; wp.
  do 3! rnd.
  skip. progress.
  by rewrite duni_ll.
  by rewrite dshort_ll.
  by smt.

  call (_:true).
  call (_:true).
  - by auto.
  progress.
  call (_:true).
  auto.
  call (_:true).
  - by auto.
  skip.
  progress.
  - by rewrite dvector_ll duniR_ll.
  - by .
qed.

lemma hop1_right &m:
  Pr[MLWE(B1(A)).main(true) @ &m : res] =
  Pr[CPA(MLWE_PKE_BASIC1,A).main() @ &m : res].
proof.
byequiv => //.
proc;inline *.
wp; call(:true); auto => /=.
call(:true); wp => /=.
rnd{1}; wp; do 2! rnd{1}.
by rnd; wp; rnd{1}; auto; smt(duni_ll dshort_ll).
qed.

end section.
(**  Lemma  1  **)
 local lemma lem_G1_G2(A<:Adversary) &m:
     Pr[G1(A).main() @ &m : res] = Pr[G2(A).main() @ &m : res].

proof.
byequiv=> //. proc.
  call (_:true).
  call (_:true).
  - by auto.
  progress.
  call (_:true).
  auto.
  call (_:true).
  - by auto.
  skip.
  progress.
  - by rewrite dvector_ll duniR_ll.
  - by .
qed.

