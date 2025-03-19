// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 69
// Jazman Mohamad Ismail: 1923072
// Arhan Chhabra: 1940198
//
// Good luck!
//
// END-TODO(Name)

method ReverseArray(a: array<int>) 
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length - 1 - i])
{
// BEGIN-TODO(IsCelebrity)
  var n := 0;
  while n < a.Length / 2
        invariant 0 <= n <= a.Length / 2
        // invariant forall i | 0 <= i < n :: a[i] == old(a[a.Length - 1 - i])
        // invariant forall i | n <= i < a.Length - 1 - i :: a[i] == old(a[i])
        // invariant forall i | a.Length - 1 - i <= i < a.Length :: a[i] == old(a[i])
        invariant forall i | 0 <= i < n :: 
                   a[i] == old(a[a.Length - 1 - i]) && a[a.Length - 1 - i] == old(a[i])
        invariant forall i | n <= i < a.Length - n :: a[i] == old(a[i])
          {
              // a[n] := a[a.Length - 1 - n];
              // n := n + 1;
              
              var tmp := a[n];
              a[n] := a[a.Length - 1 - n];
              a[a.Length - 1 - n] := tmp;
              n := n + 1;
          }
// END-TODO(IsCelebrity)
}
