include "Stack.dfy"

method Main() 
{
      // some tests
      var s := new Stack<int>();
      s.Push(1);
      s.Push(2);
      s.Push(4);
      var test := s.Pop();
      print "\n";
      print test;
      print "\n";
      test := s.Peek();
      print test;
      test := s.Peek();
      print "\n";
      print test;
      print "\n";
}