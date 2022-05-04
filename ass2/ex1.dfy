// ex1
lemma LemCNN(n: nat)
requires n >= 0
ensures (n*(n+1)) % 2 == 0
{
	if n == 0 { assert 0*(0+1) % 2 == 0; }		// base case
	else {
		LemCNN(n-1);							// prove for n-1 case
		assert n*(n+1) % 2 == (n-1)*n % 2;		// arith
		assert n*(n+1) % 2 == 0;				// arith for n >= 1

	}
}

method LemCNNTester()
{
	var n: nat;
	LemCNN(n);
	assert n*(n+1)%2 == 0;
}
