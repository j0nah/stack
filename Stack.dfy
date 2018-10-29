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
  ensures stack[0] == elem
  {
    stack := [elem] + stack;
  }

  method Pop() returns (r: T)
  modifies this;
  requires stack != [];
  ensures stack == old(stack)[1..]
  ensures r == old(stack)[0]
  {    
    r := stack[0];
    stack := stack[1..];
  } 

  method Peek() returns (r: T)
  requires stack != [];
  ensures stack == old(stack)
  ensures r == stack[0]
  {    
    return stack[0];
  } 
}