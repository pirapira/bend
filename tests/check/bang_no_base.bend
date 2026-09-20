# a ! binder runs through Base's Unit, so it needs Base.

type Nat is Data:
  Zero{}
  Succ{pred: Nat}

def twice(!f: Nat -> Nat, x: Nat) -> Nat:
  f(f(x))

#|Error:
#|- message  : import Base (a ! binder runs through Base's Unit)
#|Context:
#|- f : @_:Nat -> Nat
#|- x : Nat
#|Location: twice
#|7 | def twice(!f: Nat -> Nat, x: Nat) -> Nat:
#|8>|   f(f(x))
#|9 |
#|exit 1
