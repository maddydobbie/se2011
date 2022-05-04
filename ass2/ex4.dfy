// ex4
class Quack
{
    var buf:array<char>;
    var m:int, n:int;

    ghost var shadow: seq<char>;

    predicate Valid() reads this, this.buf
    { buf.Length!=0 && 0<=m<=n<=buf.Length && shadow==buf[m..n] }

    constructor(size: int)
    requires size > 0;
    ensures shadow == []
    ensures fresh(buf)
    ensures Valid()
    {
        buf := new char[size];
        m, n:= 0, 0;
        shadow:= [];
    }

    method Empty() returns (x: bool)
    requires Valid();
    ensures x <==> shadow==[] // an empty shadow means x is true
    ensures Valid()           // can be better to make this last
    {
       x := m==n;             // no elements means x is true
    }      

    method Push(x: char) modifies this, this.buf, this`m, this`n
    requires Valid();
    // code
    ensures if old(n)   == old(buf.Length) then fresh(buf) else buf==old(buf)
    ensures if old(n-m) == old(buf.Length) then buf.Length==2*old(buf.Length) else buf.Length==old(buf.Length)
    ensures 0<n<=buf.Length ==> buf[n-1]==x
    // shadow
    ensures |shadow|    == |old(shadow)|+1
    ensures   shadow    == old(shadow) + [x]; // new tail
    ensures Valid()
    {
        if n==buf.Length
        {
            var b:= new char[buf.Length];          // temporary
            if m==0 { b:= new char[2*buf.Length]; }// double size
            forall (i | 0<=i<n-m) { b[i]:= buf[m+i]; } // copy m..n to 0..n-m
            buf, m, n:= b, 0, n-m;                     // copy b to buf, reset m,n
        }
        buf[n], n:= x, n+1;         // now we definitely have room
        shadow:= shadow + [x];      // same as previous slide: concat 'x'
    }   

    method Pop() returns(x: char) modifies this, this`n
    requires Valid()
    requires  shadow != [] 
    // code
    ensures   buf    == old(buf)                  // buf name does not change 
    ensures   x      == old(buf[n-1])             // element n-1 is returned
    ensures   n      == old(n-1)                  // n moves down
    // shadow
    ensures |shadow| == |old(shadow)|-1           // popped an elem
    ensures   x      == old(shadow[|shadow|-1])   // last element
    ensures shadow   == old(shadow[..|shadow|-1]) // chop off tail
    ensures Valid()                               // check okay at end
    {
        x, n:= buf[n-1], n-1;                     // get tail, decr n
        shadow:= shadow[..|shadow|-1];            // chop tail off shadow
    }
///////////////////////////////////////////////////////
    // DO NOT CHANGE ANYTHING ABOVE THIS LINE //
    ////////////////////////////////////////////
	method Repair(i:nat, c:char) modifies this, this.buf
	requires Valid()
	ensures Valid()
	ensures buf.Length == old(buf.Length)
	ensures buf == old(buf)
	ensures |shadow| == |old(shadow)|
	ensures forall j :: (0 <= j < buf.Length && j != n-1-i) ==> buf[j] == old(buf[j])
	ensures i < n-m ==> buf[n-1-i] == c
	ensures i < n-m ==> shadow == old(shadow[..n-m-1-i])+[c]+old(shadow[n-m-i..])
	ensures i >= n-m ==> shadow == old(shadow)
	{
		if i < n-m 
		{
			buf[n-1-i] := c;
			shadow := shadow[..n-m-1-i]+[c]+shadow[n-m-i..];
		}	
	}
	
    ////////////////////////////////////////////
    // DO NOT CHANGE ANYTHING BELOW THIS LINE //
///////////////////////////////////////////////////////

} // end of Quack class

method Tester()
{
    var q:= new Quack(6);
    var p: char;
    var e: bool;

    q.Push('m');
    q.Push('a');
    q.Push('k');
    q.Push('e');
    q.Repair(0, 'o');                 // e --> o
    p := q.Pop();    assert p=='o';
    q.Repair(2, 'y');                 // m --> y
    p := q.Pop();    assert p=='k';
    q.Repair(3, 'x');                 // bad repair, ignored
    q.Repair(0, 'a');                 // k --> a
    p := q.Pop();    assert p=='a';
    q.Repair(2, 'x');                 // bad repair, ignored
    q.Repair(1, 'x');                 // bad repair, ignored
    p := q.Pop();    assert p=='y';

    e := q.Empty();  assert e;
    q.Repair(0, 'x');                 // bad repair, ignored
}
