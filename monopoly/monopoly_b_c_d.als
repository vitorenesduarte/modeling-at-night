open util/ordering[Time] as T0

sig Time {}

sig Espaco {}

sig Propriedade extends Espaco {
   dono : set Jogador -> Time
} {
   // * i) Cada propriedade tem no máximo um dono.
	all t : Time | lone dono.t
}

sig Avenida extends Propriedade {
   cor : one Cor,
   edificio : set Edificio -> Time
} {
   // * ii)  Cada avenida tem no máximo um edifício.
	all t : Time | lone edificio.t
}

sig Cor {}
sig Jogador {
	jogador : set Time
}

abstract sig Edificio {}
sig Casa, Hotel extends Edificio {}

fact {
   all t : Time | inv[t]
}

pred inv[t : Time] {
   // * iii)  Cada edifício pertence no máximo a uma avenida.
   all e : Edificio | lone edificio.t.e

   // * iv) Uma avenida só pode ter edifícios se tiver dono e se todas as
   // avenidas da mesma cor pertencerem ao mesmo dono
   all a : Avenida 
      | let avenidasComAMesmaCor = a.cor.~cor 
         | some a.edificio.t => a.dono.t = avenidasComAMesmaCor.dono.t

   // * v) Não é possível uma avenida ter um hotel se outra avenida da
   // mesma cor ainda não tiver nenhum edifiício
   all a : Avenida
      | let avenidasComAMesmaCor = a.cor.~cor
         | some a.edificio.t & Hotel => some avenidasComAMesmaCor.edificio.t & Casa

   // novo invariante:
   // Uma propriedade pertence a um jogador que existe
   all p : Propriedade
      | p.dono.t in jogador.t 
}

run {
   #Jogador = 1
   #Propriedade = 2
   #Edificio = 1
} for 3
