// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 69
// Jazman Mohamad Ismail: 1923072
// Arhan Chhabra: 1940198
//
// Good luck!
//
// END-TODO(Name)

module CelebrityFinderModule
{
  type Person = nat
  type People = set<Person>

  predicate knows(p: Person, q: Person)

  predicate isCelebrity(people: People, p: Person)
  {
// BEGIN-TODO(IsCelebrity)
// Implement the `isCelebrity` predicate according to the instructions.

// Everyone knows the celebrity: ∀𝑝:𝑝≠𝑐⟹𝑘𝑛𝑜𝑤𝑠(𝑝,𝑐)
// The celebrity knows no one else: ∀𝑝:𝑝≠𝑐⟹¬𝑘𝑛𝑜𝑤𝑠(𝑐,𝑝)

  (forall i :: i in people && i != p ==> knows(i, p)) &&
  (forall i :: i in people && i != p ==> !knows(p, i))


// END-TODO(IsCelebrity)
  }    

  method FindCelebrity(people: People) returns (result: Person)
// BEGIN-TODO(FindCelebrity)
// Implement the `FindCelebrity` method according to the instructions.
    requires exists c :: isCelebrity(people, c)
    requires |people| > 0 // since at least one celebrity is guarenteed
    ensures isCelebrity(people, result)
    {
      var C := people;
      var a : Person :| a in C;
      C := C - {a};

      while !(C == {})
        invariant a in people
        invariant C <= people
        invariant (forall k | k in people - C && k != a :: !isCelebrity(people, k))
        // invariant (exists c :: c in (C + {a}) && isCelebrity(people,c) && forall x :: x in people ==> (knows(x, c) && !knows(c, x)))




        // invariant forall x :: x in (people - C) ==> (knows(x, a) && !knows(a, x))
        // invariant forall x :: x in (people - C) && x != a ==> (knows(x, a)) &&
          // forall x :: x in (people - C) && x != a ==> (!knows(a, x))
        // invariant forall x :: x in (people - C) ==> !(knows(a, b))
        // invariant !(knows(a, b))
        // invariant (exists c :: c in people && isCelebrity(people, c))
        //  ==> (forall x :: (x in (people - C) && x != a) ==> knows(x, a))
        //  invariant forall x :: (x in (people - C) && x != a) ==> knows(x, a)
        // invariant forall x :: x in (people - C) && x != a ==> (knows(x, a) && !knows(a, x))
        // invariant (exists c :: c in people && isCelebrity(people, c))
        //   ==> (forall y :: y in C ==> !knows(a, y))


        decreases |C|
      {
        var b: Person :| b in C;
        C := C - {b};

        if (knows(a,b)) {
          a := b;
        }


      }

      result:= a;

    }


// END-TODO(FindCelebrity)

}
