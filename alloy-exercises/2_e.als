open util/ordering[Hora] as H0
open util/ordering[Time] as T0

sig Time {}

sig Numero {}
sig Hora {
  actual : set Time
}

sig Nome {
  agenda : Numero -> Time,
  nome : set Time
}

sig Chamada {
  numero : one Numero,
  hora : one Hora,
  chamada : set Time
}

pred inv[t : Time] {
  // * i) Um número não pode pertencer a duas pessoas diferentes
  all n : Numero | lone agenda.t.n

  // * ii) Todos os números chamados fazem parte da agenda
  all n : chamada.t.numero | n in nome.t.agenda.t

  // * iii) Não podem existir chamadas simultâneas
  all disj c1, c2 : chamada.t | c1.hora != c2.hora

  // * iv) Todas as chamadas foram feitas antes da hora actual
  let Actual = actual.t | 
    all c : chamada.t | c.hora in  H0/prevs[Actual]

  // * v) novo invariante : todos os numeros na agenda fazem parte de pessoas que existem
  agenda.t in nome.t -> Numero
  
  // * vi) novo invariante : a hora actual existe
  one actual.t
}


abstract sig Event {
  t, t' : one Time
}

// * e i) novo: acrescentar um número à agenda.
sig Novo extends Event {
  num : Numero, 
  n : Nome
} {
  some n & nome.t // a pessoa existe
  no num & (nome.t).agenda.t // o numero ainda não existe na agenda
  no chamada.t.numero & num // o numero não foi chamado
  let Actual = actual.t | some Actual and some H0/next[Actual] // existe a hora atual e a seguinte

  nome.t' = nome.t + n
  agenda.t' = agenda.t + n -> num
  actual.t' = H0/next[actual.t]
  chamada.t' = chamada.t
}

check novo_consistente {
  all e : Novo {
    inv[e.t] implies inv[e.t'] 
  }
} for 5

run show_novo {
  some e : Novo {
    inv[e.t]
  }
} for 2

// * e ii) apaga: eliminar um nome da agenda, apagando todos os números que lhe estão associados
sig Apaga extends Event {
  n : Nome
} {
  some n & nome.t // a pessoa existe
  let Actual = actual.t | some Actual and some H0/next[Actual] // existe a hora atual e a seguinte
  no agenda.t[n] & chamada.t.numero // não há chamadas neste momento para numeros desta pessoa
  
  agenda.t' = agenda.t - (n -> Numero)
  nome.t' = nome.t - n
  actual.t' = H0/next[actual.t]
  chamada.t' = chamada.t
}

check apaga_consistente {
  all e : Apaga {
    inv[e.t] implies inv[e.t']
  }
} for 5

run show_apaga {
  some e : Apaga {
    inv[e.t]
  }
} for 2


// * e iii) chamar: efectuar uma chamada para uma determinada pessoa - a chamada deve
// ficar registada com a hora actual.
// TODO
