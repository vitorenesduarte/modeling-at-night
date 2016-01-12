sig Espaco {}

sig Propriedade extends Espaco {
   dono : set Jogador
} {
   // * i) Cada propriedade tem no máximo um dono.
   lone dono
}

sig Avenida extends Propriedade {
   cor : one Cor,
   edificio : set Edificio
} {
   // * ii)  Cada avenida tem no máximo um edifício.
   lone edificio
}

sig Cor {}
sig Jogador {}

abstract sig Edificio {}
sig Casa, Hotel extends Edificio {}

fact {
   // * iii)  Cada edifício pertence no máximo a uma avenida.
   all e : Edificio | lone edificio.e

   // * iv) Uma avenida só pode ter edifícios se tiver dono e se todas as
   // avenidas da mesma cor pertencerem ao mesmo dono
   all a : Avenida 
      | let avenidasComAMesmaCor = a.cor.~cor 
         | some a.edificio => a.dono = avenidasComAMesmaCor.dono

   // * v) Não é possível uma avenida ter um hotel se outra avenida da
   // mesma cor ainda não tiver nenhum edifiício
   all a : Avenida
      | let avenidasComAMesmaCor = a.cor.~cor
         | some a.edificio & Hotel => some avenidasComAMesmaCor.edificio & Casa
}

run {
   #Jogador = 1
   #Propriedade = 2
   #Edificio = 1
} for 3
