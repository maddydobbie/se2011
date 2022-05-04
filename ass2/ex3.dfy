// ex3
predicate ooo(s:seq<int>)
requires |s| >= 2
{ 
	exists i :: 0 <= i < |s| && forall j :: (0 <= j < |s| && i != j) ==> s[i] != s[j]
	&& !exists k :: (0 <= k < |s| && k != i) && forall l :: (0 <= l < |s| && i != j && k != l) ==> s[k] != s[l]
}

method Getooo(s: seq<int>) returns (x: int)
requires |s| >=2
// ensures
{
	if (|s| == 2 && s[0] != s[1])
	{ return 0; }
	else if |s| == 2 && s[0] == s[1]
	{ return -1; }
	
	else
	{
		x := -1;
		var y:int := 0;
		var z:int := 1;
		var i:int := 2;

		while i < |s|
		invariant 0 <= i <= |s|
		{
			if s[y] != s[z] && s[i] != s[y] && s[i] != s[z]
			{ return -1; }

			if x != -1 
			{
				if s[y] == s[z] && s[y] != s[i]
				{ return -1; }
				if s[y] != s[z] && s[i] == s[y]
				{
					if x != z
					{ return -1; }
				}
				if s[y] != s[z] && s[i] == s[z] 
				{
					if x != y
					{return -1; }
				}
			}
			else 
			{
				if s[y] == s[z] && s[i] != s[y]
				{ x := i; }
				if s[y] != s[z] && s[i] == s[y]
				{ x := z; }
				if s[y] != s[z] && s[i] == s[z]
				{ x := y; }
			}
			i := i+1;
		}
		return x;
	}
} 

method Main()
{
	var s:seq<int>;
	var l:seq<int>;
	var r:int;
	s := [1,1,42,1];
	assert s[0]==1 && s[1]==1 && s[2]==42 && s[3]==1;
	assert ooo(s); // Part (i)
	r := Getooo(s); // Part (ii)
	assert r==2;

	s := [1,1,42,42];
	assert s[0]==1 && s[1]==1 && s[2]==42 && s[3]==42;
	assert !ooo(s);
	r := Getooo(s);
	assert r==-1;

	s := [1,1,1,42];
	assert s[0]==1 && s[1]==1 && s[2]==1 && s[3]==42;
	assert !ooo(s);
	r := Getooo(s);
	assert r==3;

	s := [42,1,1,1];
	assert s[0]==42 && s[1]==1 && s[2]==1 && s[3]==1;
	assert !ooo(s);
	r := Getooo(s);
	assert r==0;

	s := [1,42,1,1];
	assert s[0]==1 && s[1]==42 && s[2]==1 && s[3]==1;
	assert !ooo(s);
	r := Getooo(s);
	assert r==1;

	l := [1,1];
	assert s[0]==1 && s[1]==1;
	assert !ooo(l);
	r := Getooo(l);
	assert r==-1;

	l := [1,42];
	assert s[0]==1 && s[1]==42;
	assert ooo(l);
	r := Getooo(l);
	assert r==0;


}
