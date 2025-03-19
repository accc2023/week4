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
    // Set is not empty (we know since the instructions said that there has to be at least one celebrity)
     requires |people| > 0
     requires exists c :: c in people && isCelebrity(people, c)
     ensures isCelebrity(people, result)
    {
      var C := people;
      var a : Person :| a in C;
      C := C - {a};

      while !(C == {})
        // Following invariants hold in every iteration:

        // a needs to a person from people
        invariant a in people
        // C has to be the size of people or less
        invariant C <= people
        // Current a or another person remaining in C must be a celebrity
        invariant exists c | c in (C + {a}) :: isCelebrity(people, c)
        // Removed people must all know who the celebrity is (whoever they are from C + {a})
        invariant forall p | p in (people - C - {a}) :: exists c | c in (C + {a}) :: knows(p, c)
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
