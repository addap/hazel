module type NUM = sig 
  type t
  val one   : t
  val zero  : t
  val ( + ) : t -> t -> t
  val ( * ) : t -> t -> t
end
module type AD = sig 
  include NUM 
  type n
  val diff  : (t -> t) -> (n -> n)
  val grad  : (t * t -> t) -> (n * n -> n * n)
end
module RMAD (N : NUM) : (AD with type n = N.t) 
