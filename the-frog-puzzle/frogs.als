-- k rocks
-- n green frogs
-- m brown frogs
-- k > n+m

open util/integer as I0
open util/ordering[Time] as T0

// * SIGNATURES
sig Time {}

one sig Rocks {
   frogs: Int -> Frog -> Time
} {
   all t : Time | facts[t]
}

pred facts[t : Time] {
   // * starts a position zero -> left rock
   I0/min[keys[t]] = 0 
	
   // * in each rock, there's only one frog
   all k : keys[t] | one Rocks.frogs[k].t 

   // * all rocks have something, even if it's nothing
   let keys = keys[t], min = I0/min[keys], max = I0/max[keys] 
      | keys = range[min, max]
}

abstract sig Frog {
} {
   all f : Frog, t: Time | facts[f, t]
}

pred facts[f : Frog, t : Time] {
   // * a frog is in one rock only
   one Rocks.frogs.t.f
}

sig GreenFrog, BrownFrog, NoFrog extends Frog {} 


// * FUNCTIONS
fun keys [t : Time] : set Int {
   Rocks.frogs.t.Frog
}

fun lastKey [t : Time] : Int {
	I0/max[keys[t]]
}

fun range[min : Int, max : Int] : set Int {
   min.*I0/next & *I0/next.max
}


// * TRACES
pred init[t : Time] {
   let GreenIndexes = Rocks.frogs.t.GreenFrog,
         NoIndexes = Rocks.frogs.t.NoFrog,
         BrownIndexes = Rocks.frogs.t.BrownFrog,
         minGI = I0/min[GreenIndexes],
         maxGI = I0/max[GreenIndexes],
         minNI = I0/min[NoIndexes],
         maxNI = I0/max[NoIndexes],
         minBI = I0/min[BrownIndexes],
         maxBI = I0/max[BrownIndexes] 
            | GreenIndexes = range[minGI, maxGI]  // green frogs are consecutive
              and NoIndexes = range[minNI, maxNI]  // no frogs are consecutive
              and BrownIndexes = range[minBI, maxBI] // brown frogs are consecutive
              and minGI = 0 // green frogs are on the left 
              and some NoIndexes // there are empty rocks
              and maxBI = lastKey[t] // brown frogs are on the right
}

pred jump[g : GreenFrog, t,t' : Time] {
   let position = Rocks.frogs.t.g, 
         nextPosition = I0/plus[position, 1],
         nextNextPosition = I0/plus[position, 2]
      | (
            // * jump to an empty rock
            nextPosition in Rocks.frogs.t.NoFrog
            and let rock = Rocks.frogs.t[nextPosition]
               | Rocks.frogs.t'[position] = rock 
                 and Rocks.frogs.t'[nextPosition] = g
                 and theRestRemainsTheSame[position, nextPosition, t, t']
        )
        or
        (
           // * jump over a brown frog
           nextPosition in Rocks.frogs.t.BrownFrog
           and nextNextPosition in Rocks.frogs.t.NoFrog
           and let rock = Rocks.frogs.t[nextNextPosition]
              | Rocks.frogs.t'[position] = rock 
                and Rocks.frogs.t'[nextNextPosition] = g
                and theRestRemainsTheSame[position, nextNextPosition, t, t']
        )
}

pred jump[b : BrownFrog, t,t' : Time] {
	let position = Rocks.frogs.t.b,
         nextPosition = I0/minus[position, 1],
         nextNextPosition = I0/minus[position, 2]
      | (
            // * jump to an empty rock
            nextPosition in Rocks.frogs.t.NoFrog
            and let rock = Rocks.frogs.t[nextPosition]
               | Rocks.frogs.t'[position] = rock 
                 and Rocks.frogs.t'[nextPosition] = b
                 and theRestRemainsTheSame[position, nextPosition, t, t']
        )
        or
        (
           // * jump over a green frog
           nextPosition in Rocks.frogs.t.GreenFrog
           and nextNextPosition in Rocks.frogs.t.NoFrog
           and let rock = Rocks.frogs.t[nextNextPosition]
              | Rocks.frogs.t'[position] = rock 
                and Rocks.frogs.t'[nextNextPosition] = b
                and theRestRemainsTheSame[position, nextNextPosition, t, t']
        )
}

fact traces {
   init[T0/first]
   all t : Time - T0/last | let t' = T0/next[t]
      | not win[t] => (some g : GreenFrog | jump[g, t, t'] or some b : BrownFrog | jump[b, t, t'])
                         else theRestRemainsTheSame[-1, -1, t, t'] // if win, do nothing
}

pred win[t : Time] {
      let GreenIndexes = Rocks.frogs.t.GreenFrog,
         NoIndexes = Rocks.frogs.t.NoFrog,
         BrownIndexes = Rocks.frogs.t.BrownFrog,
         minGI = I0/min[GreenIndexes],
         maxGI = I0/max[GreenIndexes],
         minNI = I0/min[NoIndexes],
         maxNI = I0/max[NoIndexes],
         minBI = I0/min[BrownIndexes],
         maxBI = I0/max[BrownIndexes] 
            | GreenIndexes = range[minGI, maxGI]  // green frogs are consecutive
              and NoIndexes = range[minNI, maxNI]  // no frogs are consecutive
              and BrownIndexes = range[minBI, maxBI] // brown frogs are consecutive
              and maxGI = lastKey[t] // green frogs are on the right 
              and some NoIndexes // there are empty rocks
              and minBI = 0 // brown frogs are on the left
}

run {
	some t : Time | win[t]
} for 10 but exactly 2 GreenFrog, exactly 2 BrownFrog, exactly 1 NoFrog
