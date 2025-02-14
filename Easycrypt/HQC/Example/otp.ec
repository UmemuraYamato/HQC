require import AllCore.
require BitWord.

op l : { int | 0 < l } as gt0_l.

clone import BitWord as Bits with
  op n <- l
proof gt0_n by exact/gt0_l
rename
  "word" as "bitstring"
  "dunifin" as "dbitstring".

import DWord.

type message = bitstring.
type ciphertext = bitstring.
type key = bitstring.

op [lossless] dmsg : message distr.


module OTP = {
  var m: message
  var c: ciphertext

  proc kg() : key = {
    var k;

    k <$ dbitstring;
    return k;
  }

  proc enc(k: key, m: message) : ciphertext = {
    return (k +^ m);
  }

  proc main() : unit = {
    var k;

    m <$ dmsg;
    k <@ kg();
    c <@ enc(k, m);
  }
}.

module Uniform = {
  var m: message
  var c: ciphertext

  proc main() : unit = {
    m <$ dmsg;
    c <$ dbitstring;
  }
}.


lemma Secrecy : 
  equiv[ OTP.main ~ Uniform.main : true ==> (OTP.m, OTP.c){1} = (Uniform.m, Uniform.c){2} ].
proof.
  proc.
  inline{1} OTP.kg OTP.enc.
  wp.
  rnd (fun k => k +^ OTP.m{1}).
  rnd.
  skip.
  progress.
  algebra.
qed.
