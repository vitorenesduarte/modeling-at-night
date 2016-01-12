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

pred inv[t : Time]{
  // * i) Cada aluno só pode estar inscrito no máximo em duas UCEs
  all a : Aluno | #inscritos.t.a <= 2

  // * ii) Todos os alunos dos grupos de uma UCE estão inscritos nessa UCE
  all u : UCE, g : u.grupos.t, a : g.membros | a in u.inscritos.t

  // * iii) Apenas os alunos inscritos têm (no máximo uma) nota em cada UCE
  all u : UCE | u.notas.t.Nota in u.inscritos.t // apenas os alunos inscritos tem notas na UCE
  all u : UCE, a : u.inscritos.t | lone u.notas.t[a] // todos os inscritos tem no máximo uma nota

  // * iv) Cada aluno inscrito pertence apenas a um grupo em cada UCE
  all u : UCE, a : u.inscritos.t | one u.grupos.t & membros.a

  // * v) Todos os elementos de um grupo que já tem nota lançada têm a mesma nota.
  all u : UCE, g : u.grupos.t | one g.membros.(u.notas.t)
}

// c)  Especifique a operação LancaNota que lanca a nota de um aluno de uma UCE, por
// forma a garantir a sua consistência e a preservação dos invariantes.
pred lanca_nota[a : Aluno, u : UCE, n : Nota, t, t' : Time] {
  a in u.inscritos.t

  // ninguém no grupo tem notas
  let grupo = membros.a & u.grupos.t
    | no grupo.membros.(u.notas.t)
  
  let grupo = membros.a & u.grupos.t
    | notas.t' = notas.t + u -> grupo.membros -> n

  grupos.t' = grupos.t // os grupos mantêm-se
  inscritos.t' = inscritos.t // os inscritos também
}

check lanca_nota_consistente {
  all t : Time - T0/last, a : Aluno, u : UCE, n : Nota {
    let t' = T0/next[t]
      | inv[t] and lanca_nota[a, u, n, t, t'] implies inv[t']
  }
} for 5

// no instance - why?
run show_lanca_nota {
  some t : Time, a : Aluno, u : UCE, n : Nota
    | let t' = T0/next[t] | inv[t] and lanca_nota[a, u, n, t, t']
} for 3
