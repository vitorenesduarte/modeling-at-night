open util/ordering[Time] as T0

sig Time {}

sig Aluno {}

sig Grupo {
  membros : some Aluno
}

sig Nota {}

abstract sig UCE {
  inscritos : set Aluno -> Time,
  grupos : set Grupo -> Time,
  notas : Aluno -> Nota -> Time
}

one sig MFES, CSSI, SD, EA extends UCE {}

pred inv [t : Time]{
  // * i) Cada aluno só pode estar inscrito no máximo em duas UCEs
  all a : Aluno | #inscritos.t.a <= 2

  // * ii) Todos os alunos dos grupos de uma UCE estão inscritos nessa UCE
  all u : UCE, g : u.grupos.t, a : g.membros | a in u.inscritos.t

  // * iii) Apenas os alunos inscritos têm (no máximo uma) nota em cada UCE
  all u : UCE | u.notas.t.Nota in u.inscritos.t // apenas os alunos inscritos tem notas na UCE
  all u : UCE, a : u.inscritos.t | lone u.notas.t[a] // todos os inscritos tem no máximo uma nota

  // * iv) Cada aluno inscrito pertence apenas a um grupo em cada UCE
  all u : UCE, a : u.inscritos.t | lone u.grupos.t & membros.a

  // * v) Todos os elementos de um grupo que já tem nota lançada têm a mesma nota.
  all u : UCE, g : u.grupos.t | one g.membros.(u.notas.t)
}

run {
  some t : Time | inv[t]
  one Grupo
} for 3
