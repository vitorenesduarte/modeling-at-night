open util/ordering[Hora] as H0

sig Numero {}
sig Hora {}

one sig Actual in Hora {}

sig Nome {
  agenda : some Numero
}

sig Chamada {
  numero : one Numero,
  hora : one Hora
}

pred inv {
  // * i) Um número não pode pertencer a duas pessoas diferentes
  all n : Numero | lone agenda.n

  // * ii) Todos os números chamados fazem parte da agenda
  all n : Chamada.numero | n in Nome.agenda

  // * iii) Não podem existir chamadas simultâneas
  all disj c1, c2 : Chamada | c1.hora != c2.hora

  // * iv) Todas as chamadas foram feitas antes da hora actual
  all c : Chamada | c.hora in  H0/prevs[Actual]
}

run {
  inv 
} for 2
