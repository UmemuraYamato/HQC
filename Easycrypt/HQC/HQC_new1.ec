(* -------------------------------------------------------------------- *)
require import AllCore List Distr Perms ZModP DBool.
require (*--*) Subtype Monoid Ring Subtype Bigalg StdOrder StdBigop.

import StdOrder.IntOrder StdBigop.Bigreal.

  (* -------------------------------------------------------------------- *)
clone import Ring.ComRing as ZR.
clone import ZModP.ZModRing as ZM.
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

op [lossless uniform full] duniform_R : R distr.
op [lossless uniform full] duniform_nl_R : R distr.
op [lossless] dlowconstweight_Rw  : R distr. (* lowconstweight Hamming Weight = w *)
op [lossless] dlowconstweight_Re  : R distr. (* Hamming Weight = e *)
op [lossless] dlowconstweight_Rr  : R distr. (* Hamming Weight = r *)
op [lossless] dparity_Rb1  : R distr.         (* Parity = b1 *)
op [lossless] dparity_Rb2  : R distr.         (* Parity = b2 *)
op [lossless] dparity_Rb3  : R distr.         (* Parity = b3 *)

op duni = dvector duniform_R.
op duni_nl = dvector duniform_nl_R.
op dweight_w = dvector dlowconstweight_Rw.
op dweight_e = dvector dlowconstweight_Re.
op dweight_r = dvector dlowconstweight_Rr.
op dparity_b1 = dvector dparity_Rb1.
op dparity_b2 = dvector dparity_Rb2.
op dparity_b3 = dvector dparity_Rb3.

op H: vector -> matrix.
op truncate_l: vector -> vector.

const g : matrix.

pred is_lossless_R (duniform_R : R distr) = weight duniform_R = 1%r.
pred is_lossless_R_nl (duniform_nl_R : R distr) = weight duniform_nl_R = 1%r.

(** Lossless of the distribution **)

lemma dparity_b2_ll: is_lossless dparity_b2.
    proof. smt. qed.

lemma duni_ll: is_lossless duni.
    proof. smt. qed.

lemma dweight_r_ll: is_lossless dweight_r.
    proof. smt. qed.

lemma dweight_e_ll: is_lossless dweight_e.
    proof. smt. qed.

lemma dparity_b3_ll: is_lossless dparity_b3.
    proof. smt. qed.

lemma duni_nl_ll: is_lossless duni_nl.
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

    x  <$ dweight_w;              (* ZModP p=2 -> F_2 *)
    y  <$ dweight_w;
    h  <$ dparity_b1;
    h' <- (H h);               (* h -> H making for QC *)
    s <- x + h' *^ y;
    pk <- (h, s);
    sk <- (x, y);

    return (pk,sk);
  }

  proc enc(pk:pkey, m:ptxt):ctxt = {
      var e,r1,r2,u,v,h,s,h',s',c;

    (h, s) <- pk;
    e  <$ dweight_e;
    r1 <$ dweight_r;
    r2 <$ dweight_r;
    h' <- (H h);
    s' <- (H s);

    u <- r1 + h' *^ r2;
    v <- truncate_l(m ^* g + s' *^ r2 + e);

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

module UniformHQC_PKE : Scheme = {
  proc kg():pkey *skey = {
  var x,y,h,h',s,pk,sk;

    x  <$ dweight_w;              (* ZModP p=2 -> F_2 *)
    y  <$ dweight_w;
    h  <$ dparity_b1;
    h' <- (H h);               (* h -> H making for QC *)
    s <- x + h' *^ y;
    pk <- (h, s);
    sk <- (x, y);

    return (pk,sk);
  }

  proc enc(pk:pkey, m:ptxt):ctxt = {
      var e,r1,r2,u,v,h,s,h',s',c;

    (h, s) <- pk;
    e  <$ duni;
    r1 <$ duni;
    r2 <$ duni;
    h' <- (H h);
    s' <- (H s);

    u <- r1 + h' *^ r2;
    v <- truncate_l(m ^* g + s' *^ r2 + e);

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
  proc choose(pk:pkey) : ptxt * ptxt
  proc guess1(h:vector, s:vector) : pkey
  proc guess2(pk:pkey,  c:ctxt) : bool
}.

(** II_DQCSD_P Assumption **)

module II_DQCSD_P_m0(Adv : Adv_T) = {

  proc main(b : bool) : bool = {
    var pk, sk, h, s0, s1, m0, m1, c, b';

      (pk, sk) <@ HQC_PKE.kg();
      (h, s0)  <- pk;
      s1       <$ dparity_b2;
      pk       <@ Adv.guess1(if b then (h, s1) else (h, s0));

      (m0, m1) <@ Adv.choose(pk);
      c        <@ HQC_PKE.enc(pk, m0);

      b'       <@ Adv.guess2(pk, c);

    return b';
  }

}.

module II_DQCSD_P_m1(Adv : Adv_T) = {

  proc main(b : bool) : bool = {
    var pk, sk, h, s0, s1, m0, m1, c, b';

      (pk, sk) <@ HQC_PKE.kg();
      (h, s0)  <- pk;
      s1       <$ dparity_b2;
      pk       <@ Adv.guess1(if b then (h, s1) else (h, s0));

      (m0, m1) <@ Adv.choose(pk);
      c        <@ HQC_PKE.enc(pk, m1);

      b'       <@ Adv.guess2(pk, c);

    return b';
  }

}.

module B1(A : Adversary) : Adv_T = {
  proc choose(pk:pkey): ptxt * ptxt = {
  var m0, m1;
    (m0, m1) <@ A.choose(pk);
     return (m0, m1);
  }

  proc guess1(h:vector, s:vector): pkey = {
     return (h, s);
  }

  proc guess2(pk:pkey, c:ctxt) : bool = {
      var b';

    b'       <@ A.guess(pk, c);

     return b';
  }
}.

(** III_DQCSD_PT Assumption **)

module III_DQCSD_PT_m0(Adv : Adv_T) = {

  proc main(b : bool) : bool = {
    var pk, sk, h, s0, s1, m0, m1, c0, c1, b', u, v;

      (pk, sk) <@ HQC_PKE.kg();
      (h, s0)  <- pk;
      s1       <$ dparity_b2;
      pk       <- (h, s1);
      sk       <- (zerov, zerov);

      (m0, m1) <@ Adv.choose(pk);
      c0       <@ HQC_PKE.enc(pk, m0);

      u        <$ dparity_b3;
      v        <$ duni_nl;
      c1       <- (u, v);

      b'       <@ Adv.guess2(pk, if b then c1 else c0);

    return b';
  }

}.

module III_DQCSD_PT_m1(Adv : Adv_T) = {

  proc main(b : bool) : bool = {
    var pk, sk, h, s0, s1, m0, m1, c0, c1, b',u ,v;

      (pk, sk) <@ HQC_PKE.kg();
      (h, s0)  <- pk;
      s1       <$ dparity_b2;
      pk       <- (h, s1);
      sk       <- (zerov, zerov);

      (m0, m1) <@ Adv.choose(pk);
      c0       <@ HQC_PKE.enc(pk, m1);
      u        <$ dparity_b3;
      v        <$ duni_nl;
      c1       <- (u, v);

      b'       <@ Adv.guess2(pk, if b then c1 else c0);

    return b';
  }

}.

module B2(A : Adversary) : Adv_T = {
  proc choose(pk:pkey): ptxt * ptxt = {
  var m0, m1;
    (m0, m1) <@ A.choose(pk);
     return (m0, m1);
  }

  proc guess1(h:vector, s:vector): pkey = {
     return (h, s);
  }

  proc guess2(pk:pkey, c:ctxt) : bool = {
      var b';

    b'       <@ A.guess(pk, c);

     return b';
  }
}.


(** Reduction: from a PKE adversary, construct a Syndrome adversary **)

section Security.
  declare module A <: Adversary.
  declare axiom Ac_ll: islossless A.choose.
  declare axiom Ag_ll: islossless A.guess.

  (** Game Module **)
  module G1(A:Adversary) = {

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


  module G2(A:Adversary) = {

    proc main () : bool = {

    var pk: pkey;
    var sk: skey;
    var c: ctxt;
    var m0, m1: ptxt;
    var b: bool;
    var h, s: vector;

        (pk, sk) <@ HQC_PKE.kg();
        (h, s)   <- pk;
        s        <$ dparity_b2;
        pk       <- (h, s);
        sk       <- (zerov, zerov);
        (m0, m1) <@ A.choose(pk);
        c        <@ HQC_PKE.enc(pk, m0);
        b        <@ A.guess(pk, c);
        return b;
    }
  }.

  module G3 (A:Adversary) = {

    proc main () : bool = {

    var pk: pkey;
    var sk: skey;
    var c: ctxt;
    var m0, m1: ptxt;
    var b: bool;
    var h, s, u, v: vector;

        (pk, sk) <@ HQC_PKE.kg();
        (h, s)   <- pk;
        s        <$ dparity_b2;
        pk       <- (h, s);
        sk       <- (zerov, zerov);

        (m0, m1) <@ A.choose(pk);

        u        <$ dparity_b3;
        v        <$ duni_nl;
        c        <- (u, v);

        b        <@ A.guess(pk, c);
        return b;
    }
  }.
  
  module G4(A:Adversary) = {

    proc main () : bool = {
     var pk: pkey;
     var sk: skey;
     var c: ctxt;
     var m0, m1: ptxt;
     var b: bool;
     var h, s: vector;

        (pk, sk) <@ HQC_PKE.kg();
        (h, s)   <- pk;
        s        <$ dparity_b2;
        pk       <- (h, s);
        sk       <- (zerov, zerov);
        (m0, m1) <@ A.choose(pk);
        c        <@ HQC_PKE.enc(pk, m1);
        b        <@ A.guess(pk, c);
        return b;
    }
  }.

 module G5(A:Adversary) = {

    proc main () : bool = {

    var pk: pkey;
    var sk: skey;
    var c: ctxt;
    var m0, m1: ptxt;
    var b: bool;


        (pk, sk) <@ HQC_PKE.kg();
        (m0, m1) <@ A.choose(pk);
        c        <@ HQC_PKE.enc(pk, m1);
        b        <@ A.guess(pk, c);
        return b;

    }
  }.

      (** Lemma1 **)

 lemma hop1_left &m:
  Pr[G1(A).main() @ &m : res] = Pr[II_DQCSD_P_m0(B1(A)).main(false) @ &m : res].
  proof.
   byequiv=> //.
   proc. inline*. wp.
   call(_:true). wp => /=. do 3! rnd; wp => /=.
   call(_:true). wp => /=. rnd{2}. wp => /=.
   do 3! rnd.
   skip. progress.
   by rewrite dparity_b2_ll.
  qed.

 lemma hop1_right &m:
  Pr[II_DQCSD_P_m0(B1(A)).main(true) @ &m : res] = Pr[G2(A).main() @ &m : res].
  proof.
   byequiv => //.
   proc;inline *.
   wp; call(:true). wp => /=. do 3! rnd. wp => /=.
   call(:true); wp => /=.
   rnd. wp. do 3! rnd.
   skip; progress.
  qed.

 lemma G1_G2 &m :
    `| Pr[G1(A).main() @ &m : res] - Pr[G2(A).main() @ &m : res] | =
    `| Pr[II_DQCSD_P_m0(B1(A)).main(false) @ &m : res] - Pr[II_DQCSD_P_m0(B1(A)).main(true) @ &m : res] |.
  proof.
   by rewrite (hop1_left &m) (hop1_right &m).
  qed.

 (** Lemma2a **)

 lemma hop2a_left &m:
  Pr[G2(A).main() @ &m : res] = Pr[III_DQCSD_PT_m0(B2(A)).main(false) @ &m : res].
  proof.
   byequiv=> //.
   proc. inline*. wp.
   call(_:true). wp => /=. do 2! rnd{2}; wp => /=.
   do 3! rnd. wp. call(_:true). wp. rnd. wp. do 3! rnd.
   skip. progress.
   - by rewrite dparity_b3_ll.
   - by rewrite duni_nl_ll.
  qed.

 lemma hop2a_right&m:
  Pr[III_DQCSD_PT_m0(B2(A)).main(true) @ &m : res] = Pr[G3(A).main() @ &m : res].
  proof.
   byequiv=> //.
   proc. inline*. wp.
   call(_:true). wp => /=. do 2! rnd. wp => /=.
   do 3! rnd{1}. wp. call(_:true). wp. rnd. wp. do 3! rnd.
   skip. progress.
   - by rewrite dweight_e_ll.
   - by rewrite dweight_r_ll.
qed.

 lemma G2_G3 &m :
    `| Pr[G2(A).main() @ &m : res] - Pr[G3(A).main() @ &m : res] | =
    `| Pr[III_DQCSD_PT_m0(B2(A)).main(false) @ &m : res] - Pr[III_DQCSD_PT_m0(B2(A)).main(true) @ &m : res] |.
  proof.
   by rewrite (hop2a_left &m) (hop2a_right &m).
  qed.

      (** Lemma3 **)

 lemma hop3_left &m:
  Pr[G3(A).main() @ &m : res] = Pr[III_DQCSD_PT_m1(B2(A)).main(true) @ &m : res].
  proof.
   byequiv=> //.
   proc. inline*. wp.
   call(_:true). wp => /=. do 2! rnd; wp => /=.
   do 3! rnd{2}. wp. call(_:true). wp. rnd. wp. do 3! rnd.
   skip. progress.
   - by rewrite dweight_e_ll.
   - by rewrite dweight_r_ll.
  qed.

 lemma hop3_right&m:
  Pr[III_DQCSD_PT_m1(B2(A)).main(false) @ &m : res] = Pr[G4(A).main() @ &m : res].
  proof.
   byequiv=> //.
   proc. inline*. wp.
   call(_:true). wp => /=. do 2! rnd{1}. wp => /=.
   do 3! rnd. wp. call(_:true). wp. rnd. wp. do 3! rnd.
   skip. progress.
   - by rewrite dparity_b3_ll.
   - by rewrite duni_nl_ll.
qed.

 lemma G3_G4 &m :
    `| Pr[G3(A).main() @ &m : res] - Pr[G4(A).main() @ &m : res] | =
    `| Pr[III_DQCSD_PT_m1(B2(A)).main(true) @ &m : res] - Pr[III_DQCSD_PT_m1(B2(A)).main(false) @ &m : res] |.
  proof.
   by rewrite (hop3_left &m) (hop3_right &m).
 qed.

     (** Lemma4 **)

 lemma hop4_left &m:
  Pr[G4(A).main() @ &m : res] = Pr[II_DQCSD_P_m1(B1(A)).main(true) @ &m : res].
  proof.
   byequiv=> //.
   proc. inline*. wp.
   call(_:true). wp => /=. do 3! rnd; wp => /=.
   call(_:true). wp => /=. rnd. wp => /=.
   do 3! rnd.
   skip. progress.
  qed.

 lemma hop4_right &m:
  Pr[II_DQCSD_P_m1(B1(A)).main(false) @ &m : res] = Pr[G5(A).main() @ &m : res].
  proof.
   byequiv => //.
   proc;inline *.
   wp; call(:true). wp => /=. do 3! rnd. wp => /=.
   call(:true); wp => /=.
   rnd{1}. wp. do 3! rnd.
    skip; progress.
  by rewrite dparity_b2_ll.
  qed.

 lemma G4_G5 &m :
    `| Pr[G4(A).main() @ &m : res] - Pr[G5(A).main() @ &m : res] | =
    `| Pr[II_DQCSD_P_m1(B1(A)).main(true) @ &m : res] - Pr[II_DQCSD_P_m1(B1(A)).main(false) @ &m : res] |.
  proof.
   by rewrite (hop4_left &m) (hop4_right &m).
qed.

lemma Conclusion1 &m:
    `| Pr[G1(A).main() @ &m : res] - Pr[G2(A).main() @ &m : res] | + `| Pr[G2(A).main() @ &m : res] -  Pr[G3(A).main() @ &m : res] | + `| Pr[G3(A).main() @ &m : res] - Pr[G4(A).main() @ &m : res] | + `| Pr[G4(A).main() @ &m : res] - Pr[G5(A).main() @ &m : res] |
    = `| Pr[II_DQCSD_P_m0(B1(A)).main(false) @ &m : res] - Pr[II_DQCSD_P_m0(B1(A)).main(true) @ &m : res] | + `| Pr[III_DQCSD_PT_m0(B2(A)).main(false) @ &m : res] - Pr[III_DQCSD_PT_m0(B2(A)).main(true) @ &m : res] | + `| Pr[III_DQCSD_PT_m1(B2(A)).main(true) @ &m : res] - Pr[III_DQCSD_PT_m1(B2(A)).main(false) @ &m : res] | + `| Pr[II_DQCSD_P_m1(B1(A)).main(true) @ &m : res] - Pr[II_DQCSD_P_m1(B1(A)).main(false) @ &m : res] |.

  proof.
    by rewrite (G1_G2 &m) (G2_G3 &m) (G3_G4 &m) (G4_G5 &m).
  qed.

lemma Conclusion2 &m:
    `| Pr[G1(A).main() @ &m : res] - Pr[G5(A).main() @ &m : res]| <=  `| Pr[G1(A).main() @ &m : res] - Pr[G2(A).main() @ &m : res] | +  `| Pr[G2(A).main() @ &m : res] - Pr[G3(A).main() @ &m : res] | + `| Pr[G3(A).main() @ &m : res] - Pr[G4(A).main() @ &m : res] | + `| Pr[G4(A).main() @ &m : res] - Pr[G5(A).main() @ &m : res] |.
  proof. by smt. qed.

lemma Conclusion &m:
    `| Pr[G1(A).main() @ &m : res] - Pr[G5(A).main() @ &m : res] | <=  `| Pr[II_DQCSD_P_m0(B1(A)).main(false) @ &m : res] - Pr[II_DQCSD_P_m0(B1(A)).main(true) @ &m : res] | + `| Pr[III_DQCSD_PT_m0(B2(A)).main(false) @ &m : res] - Pr[III_DQCSD_PT_m0(B2(A)).main(true) @ &m : res] | + `| Pr[III_DQCSD_PT_m1(B2(A)).main(true) @ &m : res] - Pr[III_DQCSD_PT_m1(B2(A)).main(false) @ &m : res] | + `| Pr[II_DQCSD_P_m1(B1(A)).main(true) @ &m : res] - Pr[II_DQCSD_P_m1(B1(A)).main(false) @ &m : res] |.
  proof. by smt. qed.

end section Security.

print Conclusion.
