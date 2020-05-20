/*
Copyright 2020 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

import Executive;
import StandardOps;


// supposed to be a simple experiment for the procedural functionality
class ExpProcAnti0 {
    public static function main() {
        testEvidence0();

        testAnticipation0("const");
        testAnticipation0("dt2plus");
    }

    // test very simple anticipation
    public static function testAnticipation0(deadlineAlgorithm:String) {
        var reasoner:Nar = new Nar(null);
        reasoner.executive.deadlineAlgorithm = deadlineAlgorithm;

        var op = new CountOp("^x");
        reasoner.executive.acts.push({mass:1.0, act:op});

        reasoner.executive.decisionThreshold = 0.4; // set it low so it can make a descision
        reasoner.executive.dbgAnticipationVerbose = true;

        // add goal
        reasoner.input("<goal0 --> G>! :|:");

        reasoner.input("<a --> A>. :|:");
        reasoner.executive.step();
        reasoner.executive.step();

        reasoner.input("<({SELF} * a0) --> ^x>! :|:");
        reasoner.executive.step();
        op.counter = 0; // reset counter
        reasoner.executive.step();

        reasoner.input("<goal0 --> G>. :|:");
        reasoner.executive.step();
        reasoner.executive.step();

        // flush out FIFO
        for(i in 0...50) {
            reasoner.executive.step();
        }

        reasoner.input("<a --> A>. :|:");
        var wasAnticipated:Bool = false;
        for(i in 0...4) {
            reasoner.executive.step();
            
            // check if the anticipation was made
            if (reasoner.executive.anticipationsInflight.length > 0) {
                wasAnticipated = true;
            }
        }

        // check for call to ^x
        if (op.counter != 1) {
            throw "op wasn't called!";
        }

        // we require that the anticipation was made
        if (!wasAnticipated) {
            throw "Anticipation wasn't made as expected!";
        }

        Sys.println('done');
    }

    
    // test anticipation neg-confirm and revision
    public static function testEvidence0() {
        var reasoner:Nar = new Nar(null);
        reasoner.executive.randomActProb = 0.0; // disable random motor babbling
        reasoner.executive.decisionThreshold = 0.4; // enable these decisions

        // debug all the things
        reasoner.executive.dbgEvidence = true;
        reasoner.executive.dbgAnticipationVerbose = true;
        reasoner.executive.dbgDescisionMakingVerbose = true;
        reasoner.executive.dbgExecVerbose = true;
    

        reasoner.executive.acts.push({mass:1.0, act:new SwitchOp("^a")});

        reasoner.input("<b-->B>! :|:"); // add goal so it tries to exec op

        reasoner.input("<a-->A>. :|:");
        reasoner.executive.step();
        reasoner.input("<({SELF} * a0) --> ^a>! :|:");
        reasoner.executive.step();
        reasoner.input("<b-->B>. :|:");
        reasoner.executive.step();

        // flush out
        for(i in 0...100) {
            reasoner.executive.step();
        }

        reasoner.input("<a-->A>. :|:");
        reasoner.executive.step();
        reasoner.executive.randomActProb = 1.0;        // force execution of op
        //reasoner.input("<({SELF} * a0) --> ^a>! :|:");
        reasoner.executive.step();
        reasoner.executive.randomActProb = 0.0;
        
        // flush out
        for(i in 0...100) {
            reasoner.executive.step();
        }


        reasoner.executive.debugJudgements(); // print all learned judgements

        // assert that freq = 0.5!
        var found = false;
        for(i in reasoner.executive.mem.proceduralNodes.keyValueIterator()) {
            for(iImpl in i.value.implSeqs) {
                if (Math.abs(iImpl.calcFreq() - 0.5) < 0.01 ) {
                    found = true;
                }
            }
        }

        if (!found) {
            throw "Frequency is wrong! (evidence is not correctly add up)";
        }
    }
}


// op for testing if op was called
// used for self-tests, unittests, etc.
class CountOp extends Act {
    public var counter:Int = 0;

    public function new(name:String) {
        super(name);
    }

    public override function exec(args:Array<Term>) {
        counter++;
    }
}