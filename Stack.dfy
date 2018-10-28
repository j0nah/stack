class Stack<T> {
  var stack : seq<T>; // contents of stack.
  constructor ()
	{
    stack := [];
	}

  // Returns the top element of the stack, without removing it.
  method Push(elem: T)
  modifies this;
  ensures stack == [elem] + old(stack)
  {
    stack := [elem] + stack;
  }

  method Pop() returns (r: T)
  modifies this;
  requires stack != [];
  ensures stack == old(stack)[1..]
  {    
    r := stack[0];
    stack := stack[1..];
  } 
}

// method Main() 
// {
//       // some tests
//       var s := new Stack<int>();
//       s.Push(1);
//       s.Push(2);
//       s.Push(4);
//       var test := s.Pop();
//       print "\n";
//       print test;
//       print "\n";
//       test := s.Pop();
//       print "\n";
//       print test;
//       print "\n";
//       test := s.Pop();
//       print "\n";
//       print test;
//       print "\n";
}