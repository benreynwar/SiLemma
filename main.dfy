module Main {

    import XorExample

    import DP = DigraphPaths`Spec
    import CircuitToGraph

    method Main()
    {
        var b := XorExample.XorHasLoop();
        print "hello\n";
        print b;
        assert !b ==> !DP.DigraphLoop(
            CircuitToGraph.CtoG(XorExample.Xor));
    }
}