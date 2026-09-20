# a ! mark is a let's: a pattern or lambda binder takes - or +, since a
# field or an argument bound there was never checked closed.
import Base

def first(xs: List<U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{!h, t}:
      h

#|Error:
#|- message  : a - or + binder here (a ! binder is a let: !x = v)
#|Location:
#| 8 |       0
#| 9>|     case Con{!h, t}:
#|10 |       h
#|exit 1
