(* -------------------------------------------------------------------- *)
require import AllCore List Distr Perms.
require (*--*) Subtype Monoid Ring Subtype Bigalg StdOrder StdBigop.

import StdOrder.IntOrder StdBigop.Bigreal.

(* -------------------------------------------------------------------- *)
clone import Ring.ComRing as ZR.

(* -------------------------------------------------------------------- *)
clone import Bigalg.BigComRing as Big with theory CR <- ZR.

require import AllCore FSet List SmtMap CHoareTactic StdOrder.
require (*--*) BitWord Distr DInterval.
(*---*) import RealOrder RField StdBigop.Bigint BIA.
require (*--*) ROM  Matrix Ring Group ZModP PKE_CPA.

(** Construction: a Matrix **)
type matrix.
type vector.
op [lossless] dv : vector distr.

clone import Matrix as Mt with
  type vector <- vector.
  (* type matrix <- matrix.
  theory Vector.
  theory Matrix.*)

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
  proc kg(x y h s:vector):pkey *skey = {
  var pk,sk;

    x  <$ dv;
    y  <$ dv;
    h  <$ dv;
    s  <- dv; (* x + h * y;*)
    pk <- (h, s);
    sk <- (x, y);

    return (pk,sk);
  }

    proc enc(pk:pkey, m:ptxt):ctxt = {
      var e,r1,r2,u,v;
      var g : matrix;

    e <$ dseed;
    r1 <$ dseed;
    r2 <$ dseed;

    u <- r1 + h * r2;
    v <- m + s* r2 + e;

    return (u, v);
  }

  proc dec(x:skey, y:skey, u:ctxt, v:ctxt):ptxt option = {

    return Some (v - u * y);

  }
}.

(** Reduction: from a PKE adversary, construct a DDH adversary *)
module DDHAdv (A:Adversary) = {
  proc guess (gx, gy, gz) : bool = {
    var m0, m1, b, b';

    (m0, m1) <@ A.choose(gx);
    b        <$ {0,1};
    b'       <@ A.guess(gy, gz * (b?m1:m0));
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

(**Lemma 2**)
  local lemma cpa_ddh0 &m:
      Pr[CPA(ElGamal,A).main() @ &m : res] =
      Pr[DDH0(DDHAdv(A)).main() @ &m : res].
  proof.
  byequiv=> //; proc; inline *.
  swap{1} 7 -5.
  auto; call (_:true).
  auto; call (_:true).
  by auto=> /> sk _ y _ r b _; rewrite expM.
  qed.

  local module Gb = {
    proc main () : bool = {
      var x, y, z, m0, m1, b, b';

      x       <$ dt;
      y       <$ dt;
      (m0,m1) <@ A.choose(g ^ x);
      z       <$ dt;
      b'      <@ A.guess(g ^ y, g ^ z);
      b       <$ {0,1};
      return b' = b;
    }
  }.

  local lemma ddh0_ddh1 &m:


(**Lemma 4**)
  local lemma ddh1_gb &m:

      proof.
      byequiv=> //; proc; inline *.
  swap{1} 3 2; swap{1} [5..6] 2; swap{2} 6 -2.
  auto; call (_:true); wp.
 rnd (fun z, z + loge (if b then m1 else m0){2})
      (fun z, z - loge (if b then m1 else m0){2}).
 auto; call (_:true).
  auto; progress.
  - by rewrite ZPF.addrAC -ZPF.addrA ZPF.subrr ZPF.addr0.
  - by rewrite  -ZPF.addrA ZPF.subrr ZPF.addr0.
  - by rewrite expD expgK.
  qed.

  module G1(A:Adversary) = {
    proc main () : bool = {
    var x, y, z, m0, m1, b, b',gx,gy,gz,c;

      x       <$ dt;
      y       <$ dt;
      gx      <- g^x;
      gy      <- g^y;
     (m0,m1) <@ A.choose(g ^ x);
      b       <$ {0,1};
      z       <$ dt;
      gz      <- g^z;
      c <- (gy, gz * (b?m1:m0)) ;
      b'      <@ A.guess(c);
      return b' = b;
    }
  }.

   module G2(A:Adversary) = {
    proc main () : bool = {
      var x, y, z, m0, m1, b, b',gx,gy,gz,c;

      x       <$ dt;
      y       <$ dt;
      gx      <- g^x;
      gy      <- g^y;
      (m0,m1) <@ A.choose(g ^ x);
      z       <$ dt;
      gz      <- g^z;
      c <-      (gy,gz) ;
      b'      <@ A.guess(c);
      b       <$ {0,1};
      return b' = b;
    }
  }.

(**Lemma 5**)
 local lemma lem_G1_G2(A<:Adversary) &m:
     Pr[G1(A).main() @ &m : res] = Pr[G2(A).main() @ &m : res].

proof.
 byequiv => //.
 proc.
 swap{2} 10 -4.
 call ( _:true ).
  wp.
  rnd
      (fun z, z + loge (if b then m1 else m0){2})
      (fun z, z - loge (if b then m1 else m0){2}).
 rnd.
 call (_:true).
 wp.
 rnd.
 rnd.
 skip .
 progress.
  - by rewrite ZPF.addrAC -ZPF.addrA ZPF.subrr ZPF.addr0.
  - by rewrite  -ZPF.addrA ZPF.subrr ZPF.addr0.
  - by rewrite expD expgK.
qed.`


local lemma lema_G1_DDH1(A<:Adversary) &m:
     Pr[G1(A).main() @ &m : res] = Pr[DDH1(DDHAdv(A)).main() @ &m : res].

proof.
 byequiv=> //.
 proc.

  local lemma Gb_half &m:
     Pr[Gb.main()@ &m : res] = 1%r/2%r.
  proof.
 byphoare=> //; proc.
  rnd  (pred1 b')=> //=.
  conseq (: _ ==> true).
    + by move=> /> b; rewrite dbool1E pred1E.
    islossless;[ apply Ag_ll | apply Ac_ll].
qed.

  lemma conclusion &m :
    `| Pr[CPA(ElGamal,A).main() @ &m : res] - 1%r/2%r | =
    `| Pr[DDH0(DDHAdv(A)).main() @ &m : res] -
         Pr[DDH1(DDHAdv(A)).main() @ &m : res] |.
proof.
  by rewrite (cpa_ddh0 &m) (ddh1_gb &m) (Gb_half &m).
  qed.
end section Security.
print conclusion.
