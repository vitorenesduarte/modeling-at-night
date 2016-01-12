open util/ordering[Time] as T0

sig Time {}

sig Espaco {}

sig Propriedade extends Espaco {
   dono : set Jogador -> Time
} {
   // * b i) Cada propriedade tem no máximo um dono.
	all t : Time | lone dono.t
}

sig Avenida extends Propriedade {
   cor : one Cor,
   edificio : set Edificio -> Time
} {
   // * b ii)  Cada avenida tem no máximo um edifício.
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
   // * b iii)  Cada edifício pertence no máximo a uma avenida.
   all e : Edificio | lone edificio.t.e

   // * b iv) Uma avenida só pode ter edifícios se tiver dono e se todas as
   // avenidas da mesma cor pertencerem ao mesmo dono
   all a : Avenida 
      | let avenidasComAMesmaCor = a.cor.~cor 
         | some a.edificio.t => a.dono.t = avenidasComAMesmaCor.dono.t

   // * b v) Não é possível uma avenida ter um hotel se outra avenida da
   // mesma cor ainda não tiver nenhum edifiício
   all a : Avenida
      | let avenidasComAMesmaCorMenosEsta = a.cor.~cor - a
         | some a.edificio.t & Hotel
            => all outra : avenidasComAMesmaCorMenosEsta | some outra.edificio.t

   // * b) novo invariante:
   // Uma propriedade pertence a um jogador que existe
   all p : Propriedade
      | p.dono.t in jogador.t 
}

// * c i)
pred compra[j : Jogador, p : Propriedade, t,t' : Time] {
   no p.dono.t // a propriedade não tem dono
   j in jogador.t and j in jogador.t' // o jogador existe agora e depois
   p.dono.t' = j
}

pred show_compra {
   some j : Jogador, p : Propriedade, t : Time | let t' = T0/next[t] | compra[j, p, t, t']
}

run show_compra for 3

// * c ii)
