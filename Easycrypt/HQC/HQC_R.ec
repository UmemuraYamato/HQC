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
    h  <$ dshort;
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

module type Adversary = {
  proc choose(pk:pkey) : ptxt * ptxt
  proc guess(pk:pkey, c:ctxt) : bool
}.

(** Reduction: from a PKE adversary, construct a Syndrome adversary **)
module DQCSD_Adv (A:Adversary) = {
  proc guess (pk:pkey, c:ctxt) : bool = {
    var m0, m1, b, b';

    (m0, m1) <@ A.choose(pk);
    b        <$ {0,1};
    b'       <@ A.guess(pk, c);
    return b' = b;
  }
}.

(** We now prove that, for all adversary A, we have:
      `| Pr[CPA(ElGamal,A).main() @ &m : res] - 1%r/2%r |
      = `| Pr[DDH0(DDHAdv(A)).main() @ &m : res]
    - Pr[DDH1(DDHAdv(A)).main() @ &m : res] |.        **)
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

