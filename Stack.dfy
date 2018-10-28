class Stack {
  var arr : array<int>; // contents of stack.
  var top:int;
  method New(c : int)
  modifies this;
  requires c > 0; 
  ensures fresh(arr); // ensures arr is a newly created object.
  ensures this.arr.Length == c;
  ensures this.top == -1;
  ensures this.arr.Length > 0;
  {
    this.top := -1;
    this.arr := new int[c];
  }

  // Returns the top element of the stack, without removing it.
  method Push(elem: int)
  modifies this;
  modifies arr;
  requires arr.Length > 0;
  requires this.top >= -1;
  requires top < arr.Length;
  ensures top + 1 < (arr.Length - 1) ==> top == 1 + old(top);
  ensures 0 <= (old(this.top) + 1) < arr.Length - 1 ==> this.arr[old(this.top) + 1] == elem;
  ensures top < arr.Length;
  ensures old(arr.Length) == arr.Length;
  ensures forall i :: 0 <= i < top ==> old(arr[i]) == arr[i];
  ensures arr == old(arr) // required because of references
  ensures 0 <= (old(this.top) + 1) < arr.Length - 1 && ( 0 <= top < arr.Length ) ==> this.arr[top] == elem;
  {
    if( (top + 1) <= arr.Length - 1 ) {
      top := top + 1;
      arr[top] := elem;
    }
  }

  method Print() 
  {
    var n := top + 1;
    var i := 0;
    print "\n";
    print "------------";
    print "\n";
    print top;
    print "\n";
    print "************";
    print "\n";
    while(i < arr.Length) 
    decreases arr.Length-i;
    invariant 0 <= i <= arr.Length;
    {
      print arr[i];
      print "\n";
      i := i + 1;
    }
  }

  method Pop() returns (elem : int) 
  modifies this;
  requires -1 <= top < arr.Length;
  ensures arr == old(arr) // required because of references 
  ensures 0 <= old(top) < arr.Length ==> elem == arr[old(top)];
  ensures -1 <= top < arr.Length;
  {
    if(top >= 0 && top < arr.Length) {
      top := top - 1;
      elem := arr[top+1];
    } else {
      elem := -1;
    }
    return elem;
  }
}
method Main() 
{
      // some tests
      var s := new Stack;
      s.New(3);
      assert s.arr.Length > 0;
      s.Push(1);
      s.Push(2);
      s.Push(3);
      s.Push(4);
      var one := s.Pop();
      var two := s.Pop();
      var three := s.Pop();
      var four := s.Pop();

      s.Print();
}