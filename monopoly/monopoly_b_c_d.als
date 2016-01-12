open util/ordering[Time] as T0

sig Time {}

sig Espaco {}

sig Propriedade extends Espaco {
   dono : set Jogador -> Time
}

sig Avenida extends Propriedade {
   cor : one Cor,
   edificio : set Edificio -> Time
} 

sig Cor {}
sig Jogador {
	jogador : set Time
}

abstract sig Edificio {}
sig Casa, Hotel extends Edificio {}

pred inv[t : Time] {
   // * b i) Cada propriedade tem no máximo um dono.
   all p : Propriedade | lone p.dono.t

   // * b ii)  Cada avenida tem no máximo um edifício.
   all a : Avenida | lone a.edificio.t

   // * b iii)  Cada edifício pertence no máximo a uma avenida.
   all e : Edificio | lone edificio.t.e

   // * b iv) Uma avenida só pode ter edifícios se tiver dono e se todas as
   // avenidas da mesma cor pertencerem ao mesmo dono
   all a : Avenida 
      | let avenidasComAMesmaCorMenosEsta = a.cor.~cor - a
         | some a.edificio.t
            => all outra : avenidasComAMesmaCorMenosEsta |  a.dono.t = outra.dono.t

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

   // * b) novo invariante:
   // Uma avenida só pode ter edificios se tiver dono
   all a : Avenida
      | some a.edificio.t => some a.dono.t
}

// * c i) Compra de uma determinada propriedade por um determinado jogador.
pred compra[j : Jogador, p : Propriedade, t,t' : Time] {
   no p.dono.t // a propriedade não tem dono
   j in jogador.t // o jogador existe
   p.dono.t' = j
   all p_ : Propriedade - p | p_.dono.t' = p_.dono.t
   edificio.t' = edificio.t
   jogador.t' = jogador.t
}

check compra_consistente {
   all t : Time - T0/last, j : Jogador, p : Propriedade {
      let t' = T0/next[t]
         | inv[t] and compra[j, p, t, t'] implies inv[t']
   }
} for 5

run show_compra {
   some t : Time, j : Jogador, p : Propriedade
      | let t' = T0/next[t] | inv[t] and compra[j, p, t, t']
} for 2

// * c ii) Edificação numa determinada avenida, garantindo que primeiro
// se constrói uma casa e só depois desta um hotel.
pred constroi[a : Avenida, t, t' : Time] {
   some a.dono.t // a avenida tem dono
   let avenidasComAMesmaCorMenosEsta = a.cor.~cor - a {
      all outra : avenidasComAMesmaCorMenosEsta | a.dono.t = outra.dono.t
   
      no a.edificio.t => {
         some c : Casa {
            c not in Avenida.edificio.t
            a.edificio.t' = c
         }
      } else some a.edificio.t & Casa => {
         all outra : avenidasComAMesmaCorMenosEsta | some outra.edificio.t
         some h : Hotel {
            h not in Avenida.edificio.t
            a.edificio.t' = h
         }
      } else a.edificio.t' = a.edificio.t
   }

   all a_ : Avenida - a | a_.edificio.t' = a_.edificio.t
   dono.t' = dono.t
   jogador.t' = jogador.t
}

check constroi_consistente {
   all t : Time - T0/last, a : Avenida {
      let t' = T0/next[t]
         | inv[t] and constroi[a, t, t'] implies inv[t']
   }
} for 5

run show_constroi {
   some t : Time, a : Avenida
      | let t' = T0/next[t] | inv[t] and constroi[a, t, t'] and a.edificio.t != a.edificio.t'
} for 2


