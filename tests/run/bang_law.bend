# ! for a proposition: a refutation of A, under !, refutes A twice over.
# a law clause takes ! like a def binder, and its proof uses the
# hypothesis as often as it likes.
import Base

law both:
  for -A: Type
  for !n: A -> Empty
  for x: A
  for y: A
  Pair(Empty, Empty)

def both(A, n, x, y):
  (n(x), n(y))

law main:
  U32

def main():
  0

#|0
