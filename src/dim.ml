
type    zero = unit
type 'd succ = unit * 'd

type     one = zero succ
type     two = one  succ
type   three = two  succ
