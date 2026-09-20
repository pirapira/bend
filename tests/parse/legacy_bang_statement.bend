# audit: the legacy `! x = v;` statement spelling is gone from the
# grammar: a ! let is `!x = v`, the mark glued to its name as - and +
# are, so a spaced '!' is a parse error at a term position.
# ported from bend3: bend has no ![..] buffer form either
import Base

law main:
  U32

def main(): ! x = 1; x

#|Error:
#|- expected : a name after ! (a ! let binds a name: !x = v)
#|- observed : ' '
#|Location:
#| 9 | 
#|10>| def main(): ! x = 1; x
#|11 |
#|exit 1
