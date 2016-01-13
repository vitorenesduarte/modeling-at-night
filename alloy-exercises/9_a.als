sig Camaleao  {
  cor : one Cor,
  encontra : lone Camaleao
}

abstract sig Cor {}
one sig Vermelho, Azul, Verde extends Cor {}

pred inv {
  // * a i) Um camaleao não se encontra com ele próprio.
  all c : Camaleao | let partner = c.encontra| some partner => partner != c

  // * a ii) Os encontros são reciprocos. -> encontra é simétrica
  ~encontra in encontra
}

run {
  inv
  some encontra
} for 3
