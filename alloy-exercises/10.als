sig State {}

sig A {
  r, s, t : set State
}

pred implicit[a : A, pre, pos : State] {
  r.pos = r.pre + a
}

pred X[a : A, pre, pos : State] {
  s.pos != s.pre
  s.pos = s.pre + a
}

pred Y[a : A, pre, pos : State] {
  t.pos != t.pre
  t.pos = t.pre + a
}

// as implicações (a seguir) também são verdade quando ambos os lados são falsos
// isto significa que devo, por exemplo, pôr "s.pos = s.pre" no Y?
// s.pos != s.pre implies this in X
// t.pos != t.pre implies this in Y

run {

} for 3
