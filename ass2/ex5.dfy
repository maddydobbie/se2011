// ex5 
method Prison(all: set<nat>, inlight:bool) returns (swch: set<nat>)
requires |all| > 1
ensures |swch|+1 == |all|
ensures swch < all
decreases *
{
	swch := {};
	var swch2: set<nat> := {}; 				// secondary set to measure second visit
	var light: bool := inlight;
	var counter: nat :| counter in all;		// choose element to do counting

	var count:nat := 0;
	while count < 2*|all|-2					// count to 2*|all|-2
	invariant count <= 2*|all|-2
	invariant counter !in swch				// counter never turns light on
	invariant counter !in swch2
	invariant swch2 <= swch < all
//	invariant count != 0 ==> |swch| + |swch2| == count + if light then 1 else 0
//	invariant light && count != 0 ==> |swch| + |swch2| == count+1
//	invariant !light ==> |swch| + |swch2| == count 
//	invariant (|swch| + |swch2| == count) || (|swch| + |swch2| == count-1) || (|swch| + |swch2| == count+1)
//	invariant count == 2*|all|-2 ==> |swch|+1==|all|
//	invariant inlight ==> (|swch| + |swch2| == count) || (|swch| + |swch2| == count+1)
//	invariant !inlight ==> (|swch| + |swch2| == count) || (|swch| + |swch2| == count-1)
//	invariant inlight ==> count >= |swch|
//	invariant !inlight ==> count <= |swch|
//	invariant !inlight && !light ==> count == |swch| + |swch2|
//	invariant inlight ==> |swch| == count - |swch*swch2| 
	decreases *
	{
		var p :| p in all;					// choose prisoner
		if light {
			if p == counter 
				{ light := false; count := count+1; }
		}
		else {
			if p != counter && p in swch && p !in swch2
				{ light := true; swch2 := swch2 + {p}; }
			if p != counter && p !in swch 
				{ light := true; swch := swch + {p}; }
		}
	}
	LemSubsetCard(swch + {counter}, all);	// need cardinalities
	print swch + {counter};
	assert swch + {counter} == all;			// assert all been interrogated
}

lemma {:induction false} LemSubsetCard<T>(a:set<T>, b:set<T>)
ensures a==b ==> |a|==|b| 				// sets are equal (included for completeness)
ensures a<b ==> |a|<|b| 				// proper subset
{ // Level 3
	if a==b { assert |a|==|b|; } 		// Dafny knows this (added for completeness)
	else
	if a<b { 							// now handle a proper subset
		var e :| e in b-a; 				// pick an element in b that is not in a
		if a == b-{e} { 				// base case: b has 1 extra element
			assert |a| == |b|-1; 		// cardinalities of if-condition
			assert |a| < |b|; 			// trivial from previous line
		}
		else {
			LemSubsetCard(a, b-{e}); 	// IH
			assert |a| < |b-{e}|; 		// postcondition of IH
			assert |a| < |b|-1; 		// cardinality of {e} is 1
			assert |a| < |b|; 			// trivial from previous line
		}
	}
}
