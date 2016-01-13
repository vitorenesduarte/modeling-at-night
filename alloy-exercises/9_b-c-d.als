open util/ordering[Time] as T0

sig Time {}

sig Camaleao  {
  cor : Cor -> Time,
  encontra : Camaleao -> Time
}

abstract sig Cor {}
one sig Vermelho, Azul, Verde extends Cor {}

pred inv [t : Time]{
  // só tem uma cor
  all c : Camaleao | one c.cor.t

  // um encontro no máximo
  all c : Camaleao | lone c.encontra.t

  // * a i) Um camaleao não se encontra com ele próprio.
  all c : Camaleao | let partner = c.encontra.t | some partner => partner != c

  // * a ii) Os encontros são reciprocos. -> encontra é simétrica
  ~(encontra.t) in encontra.t
}

abstract sig Event {
  t, t' : Time
}

sig Encontro extends Event {
  c1, c2 : Camaleao
} {
  c1 != c2 // são camaleões diferentes
  all c : Camaleao - c1 - c2 | c.cor.t' = c.cor.t // as cores dos outros mantém-se

  // ainda não se encontram com ninguém
  no c1.encontra.t
  no c2.encontra.t
  
  encontra.t' = encontra.t + c1 -> c2 + c2 -> c1
  let nova_cor = c1.cor.t // ambos ficam com a cor do c1
    | c1.cor.t' = nova_cor and c2.cor.t' = nova_cor
}

check encontro_consistente {
  all e : Encontro | inv[e.t] implies inv[e.t']
} for 5 but 2 Time


pred uniforme [t : Time] {
  one Camaleao.cor.t
}

pred init[t : Time] {
  inv[t]
  Camaleao.cor.t = Vermelho + Azul + Verde
}

fact traces {
  init[T0/first]  

  all pre : Time - T0/last | let pos = T0/next[pre] {
    not uniforme[pre] => one e : Encontro | e.t = pre and e.t' = pos
  }
}

run uniforme {
  some t : Time | uniforme[t]
} for 10
