# a ! scrutinee is refused: a recipe is no value. pass it to a def that
# matches it.
import Base

def len(!xs: List<U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n

#|Error:
#|- message  : a - or plain scrutinee (a ! binder is a recipe, not a value: pass it to a def that matches it)
#|Location: len
#|6 |   match xs:
#|7>|     case Nil{}:
#|8 |       0n
#|exit 1
