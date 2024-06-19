
require Matrix.

type vector.

type x.

clone import Matrix as Mt with
type vector <- vector.


module A = {
  proc main(x y:vector) : vector = {

   x <- y.[1] ;

    return (x);
  }
}.

