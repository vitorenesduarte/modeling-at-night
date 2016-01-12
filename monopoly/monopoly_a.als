sig Espaco {}

sig Propriedade extends Espaco {
   dono : set Jogador
} 

sig Avenida extends Propriedade {
   cor : one Cor,
   edificio : set Edificio
}

sig Cor {}
sig Jogador {}

abstract sig Edificio {}
sig Casa, Hotel extends Edificio {}

pred inv {
   // * i) Cada propriedade tem no máximo um dono.
   all p : Propriedade | lone p.dono

   // * ii)  Cada avenida tem no máximo um edifício.
   all a : Avenida | lone a.edificio

   // * iii)  Cada edifício pertence no máximo a uma avenida.
   all e : Edificio | lone edificio.e

   // * iv) Uma avenida só pode ter edifícios se tiver dono e se todas as
   // avenidas da mesma cor pertencerem ao mesmo dono
   all a : Avenida 
      | let avenidasComAMesmaCorMenosEsta = a.cor.~cor - a
         | some a.edificio
            => all outra : avenidasComAMesmaCorMenosEsta |  a.dono = outra.dono

   // * v) Não é possível uma avenida ter um hotel se outra avenida da
   // mesma cor ainda não tiver nenhum edifiício
   all a : Avenida
      | let avenidasComAMesmaCorMenosEsta = a.cor.~cor - a
         | some a.edificio & Hotel
            => all outra : avenidasComAMesmaCorMenosEsta | some outra.edificio
}

run {
   inv
   #Jogador = 1
   #Propriedade = 2
   #Edificio = 1
} for 3
