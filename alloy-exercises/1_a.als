sig Aluno {}

sig Grupo {
  membros : some Aluno
}

sig Nota {}

abstract sig UCE {
  inscritos : set Aluno,
  grupos : set Grupo,
  notas : Aluno -> Nota
}

one sig MFES, CSSI, SD, EA extends UCE {}

pred inv {
  // * i) Cada aluno só pode estar inscrito no máximo em duas UCEs
  all a : Aluno | #inscritos.a <= 2

  // * ii) Todos os alunos dos grupos de uma UCE estão inscritos nessa UCE
  all u : UCE, g : u.grupos, a : g.membros | a in u.inscritos

  // * iii) Apenas os alunos inscritos têm (no máximo uma) nota em cada UCE
  all u : UCE | u.notas.Nota in u.inscritos // apenas os alunos inscritos tem notas na UCE
  all u : UCE, a : u.inscritos | lone u.notas[a] // todos os inscritos tem no máximo uma nota

  // * iv) Cada aluno inscrito pertence apenas a um grupo em cada UCE
  all u : UCE, a : u.inscritos | one u.grupos & membros.a

  // * v) Todos os elementos de um grupo que já tem nota lançada têm a mesma nota.
  all u : UCE, g : u.grupos | one g.membros.(u.notas)
}

run {
  inv
  one Grupo
} for 3
