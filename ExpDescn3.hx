/*
Copyright 2020 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

import Executive;

class ExpDescn3 {
    // helper for testing etc
    // builds a op-call without an argument
    public static function buildCallOp(name:String):Term {
        return Term.Cop("-->", Term.Prod([Term.Set("{", [Term.Name("SELF")])]), Term.Name(name));
    }
    
    // tests if the executive can confirm a anticipation correctly
    public static function testAnticipationConfirm1() {
        var uut:Executive = new Executive();
        uut.randomActProb = 0.0; // we must disable random actions

        { // add anticipation which is assumed to be inflight
            var pair = new Pair(uut.createStamp());
            pair.effect = new Par([Term.Name("a")]);

            uut.anticipationsInflight.push(new InflightAnticipation(pair, 5));
        }
        
        uut.step([Term.Name("a"), Term.Name("b")]);

        Assert.enforce(uut.anticipationsInflight.length == 0, "anticipation must have been confirmed!");
    }
    
    // tests if the executive can confirm a anticipation correctly
    public static function testAnticipationConfirm2() {
        var uut:Executive = new Executive();
        uut.randomActProb = 0.0; // we must disable random actions

        { // add anticipation which is assumed to be inflight
            var pair = new Pair(uut.createStamp());
            pair.effect = new Par([Term.Name("a"), Term.Name("b")]);

            uut.anticipationsInflight.push(new InflightAnticipation(pair, 5));
        }
        
        uut.step([Term.Name("a")]);

        Assert.enforce(uut.anticipationsInflight.length == 1, "anticipation must not have been confirmed!");
    }

    // tests if it builds the impl seq even when a empty trace item is present
    public static function testTraceEmpty1() {
        var uut:Executive = new Executive();
        uut.step([Term.Name("a")]);
        uut.step([buildCallOp("^b")]);
        uut.step([]);
        uut.step([Term.Name("c")]);


        // debug all evidence
        //Sys.println('');
        //for(iEvidence in uut.mem.pairs) {
        //    Sys.println(iEvidence.convToStr());
        //}

        Assert.enforce(uut.mem.pairs.length == 1, "must contain the impl seq!");
    }

    // test if it tries to fullfill a goal
    public static function testGoalFullfill1() {
        var uut:Executive = new Executive();

        var op = new CountOp("^x");
        uut.acts.push({mass:1.0, act:op});

        {
            var pair = new Pair(uut.createStamp());
            pair.condops = [new CondOps(new Par([Term.Name("b")]), [buildCallOp("^x")])];
            pair.effect = new Par([Term.Name("g")]);
            uut.mem.pairs.push(pair);
        }
        uut.goalSystem.eternalGoals.push(Term.Name("g"));
        for(t in 0...150) {
            uut.step([Term.Name("b")]);
        }

        Assert.enforce(op.counter > 0, "op must have been called!");
    }

    // patricks test from MSC
    public static function testGoalFullfill3() {
        var uut:Executive = new Executive();

        var opX = new CountOp("^x");
        var opY = new CountOp("^y");
        uut.acts.push({mass:1.0, act:opX});
        uut.acts.push({mass:1.0, act:opY});

        uut.goalSystem.eternalGoals.push(Term.Name("g"));


        uut.step([Term.Name("a")]);
        uut.step([buildCallOp("^x")]);
        uut.step([Term.Name("b")]);

        // flood sequence out of memory
        for(i in 0...50) {
            uut.step([]);
        }

        uut.step([Term.Name("b")]);
        uut.step([buildCallOp("^y")]);
        uut.step([Term.Name("c")]);
        uut.step([Term.Name("g")]);

        opX.counter = 0;
        opY.counter = 0;

        // flood sequence out of memory
        for(i in 0...50) {
            uut.step([]);
        }

        uut.step([Term.Name("a")]);
        uut.step([]);
        uut.step([]);
        uut.step([]);
        uut.step([]);
        uut.step([]);
        uut.step([Term.Name("b")]);

        for(t in 0...100) {
            uut.step([]);
        }

        // debug all evidence
        Sys.println('evidence:');
        for(iEvidence in uut.mem.pairs) {
            Sys.println(iEvidence.convToStr());
        }

        Assert.enforce(opX.counter > 0 && opY.counter > 0, "ops must have been called!");
    }

    // test if it tries to fullfill a goal when it is already fullfilled
    public static function testGoalFullfillIfSatisfied1() {
        var uut:Executive = new Executive();

        var op = new CountOp("^x");
        uut.acts.push({mass:1.0, act:op});

        {
            var pair = new Pair(uut.createStamp());
            pair.condops = [new CondOps(new Par([Term.Name("b")]), [buildCallOp("^x")])];
            pair.effect = new Par([Term.Name("g")]);
            uut.mem.pairs.push(pair);
        }
        uut.goalSystem.eternalGoals.push(Term.Name("g"));
        for(t in 0...500) {
            uut.step([Term.Name("g"), Term.Name("b")]);
        }

        Assert.enforce(op.counter == 0, "op must not have been called!");
    }

    // test if it tries to fullfill a goal when it is already fullfilled
    public static function testGoalFullfillIfSatisfied2() {
        var uut:Executive = new Executive();

        var op = new CountOp("^x");
        uut.acts.push({mass:1.0, act:op});
        
        {
            var pair = new Pair(uut.createStamp());
            pair.condops = [new CondOps(new Par([Term.Name("a")]), [buildCallOp("^x")])];
            pair.effect = new Par([Term.Name("b")]);
            uut.mem.pairs.push(pair);

        }

        {
            var pair = new Pair(uut.createStamp());
            pair.condops = [new CondOps(new Par([Term.Name("b")]), [buildCallOp("^x")])];
            pair.effect = new Par([Term.Name("g")]);
            uut.mem.pairs.push(pair);
        }
        uut.goalSystem.eternalGoals.push(Term.Name("g"));
        for(t in 0...500) {
            uut.step([Term.Name("g"), Term.Name("a")]);
        }

        Assert.enforce(op.counter == 0, "op must not have been called!");
    }

    // test forward chainer with implicit length = 2
    public static function testGoalFullfillChain2_1() {
        var uut:Executive = new Executive();

        uut.goalSystem.eternalGoals.push(Term.Name("e"));


        var opA = new TermInjOp("^a", uut, Term.Name("b"));
        var opB = new TermInjOp("^b", uut, Term.Name("c"));
        var opC = new TermInjOp("^c", uut, Term.Name("d"));
        var opD = new TermInjOp("^d", uut, Term.Name("e"));
        uut.acts.push({mass:1.0, act:opA});
        uut.acts.push({mass:1.0, act:opB});
        uut.acts.push({mass:1.0, act:opC});
        uut.acts.push({mass:1.0, act:opD});


        uut.step([Term.Name("a")]);
        uut.step([buildCallOp("^a")]);
        uut.step([Term.Name("b")]);

        // flood sequence out of memory
        for(i in 0...50) {
            uut.step([]);
        }

        uut.step([Term.Name("b")]);
        uut.step([buildCallOp("^b")]);
        uut.step([Term.Name("c")]);

        // flood sequence out of memory
        for(i in 0...50) {
            uut.step([]);
        }

        uut.step([Term.Name("c")]);
        uut.step([buildCallOp("^c")]);
        uut.step([Term.Name("d")]);

        // flood sequence out of memory
        for(i in 0...50) {
            uut.step([]);
        }

        uut.step([Term.Name("d")]);
        uut.step([buildCallOp("^d")]);
        uut.step([Term.Name("e")]);

        // flood sequence out of memory
        for(i in 0...50) {
            uut.step([]);
        }

        opA.counter = 0;
        opB.counter = 0;
        opC.counter = 0;
        opD.counter = 0;

        uut.step([Term.Name("a")]);
 
        for(t in 0...1000) {
            var events = [];
            for(ie in opA.queue) {
                events.push(ie);
            }
            for(ie in opB.queue) {
                events.push(ie);
            }
            for(ie in opC.queue) {
                events.push(ie);
            }
            for(ie in opD.queue) {
                events.push(ie);
            }
            opA.queue=[];
            opB.queue=[];
            opC.queue=[];
            opD.queue=[];

            uut.step(events);
        }

        // debug all evidence
        Sys.println('');
        for(iEvidence in uut.mem.pairs) {
            Sys.println(iEvidence.convToStr());
        }

        Assert.enforce(opD.counter > 0, "ops must have been called!");
    }



    // see if it picks up a 5 element sequence correctly
    public static function dbgSeq5() {
        var uut:Executive = new Executive();


        var opA = new CountOp("^a");
        var opB = new CountOp("^b");
        uut.acts.push({mass:1.0, act:opA});
        uut.acts.push({mass:1.0, act:opB});


        uut.step([Term.Name("a")]);
        uut.step([buildCallOp("^a")]);
        uut.step([Term.Name("b")]);
        uut.step([buildCallOp("^b")]);
        uut.step([Term.Name("c")]);


        // debug all evidence
        Sys.println('');
        for(iEvidence in uut.mem.pairs) {
            Sys.println(iEvidence.convToStr());
        }
    }

    // see if it executes 5 element sequence correctly
    public static function seq5Exec() {
        var uut:Executive = new Executive();
        {
            var p:Pair = new Pair(uut.createStamp());
            p.effect = new Par([Term.Name("g")]);
            p.condops.push( new CondOps(new Par([Term.Name("a")]), [buildCallOp("^x")]));
            p.condops.push( new CondOps(new Par([Term.Name("b")]), [buildCallOp("^y")]));
            uut.mem.addPair(p);
        }

        uut.goalSystem.eternalGoals.push(Term.Name("g"));


        var opA = new CountOp("^x");
        var opB = new CountOp("^y");
        uut.acts.push({mass:1.0, act:opA});
        uut.acts.push({mass:1.0, act:opB});


        uut.step([Term.Name("a")]);
        uut.step([buildCallOp("^x")]);
        uut.step([Term.Name("b")]);

        uut.step([]);
        uut.step([]);
        uut.step([]);
        uut.step([]);


        // debug all evidence
        Sys.println('Evidence:');
        for(iEvidence in uut.mem.pairs) {
            Sys.println(iEvidence.convToStr());
        }

        Assert.enforce(opB.counter > 0, "ops must have been called!");

    }




    public static function main() {
        //dbgSeq5(); // just for debugging

        // was just to test to see if it indeed builds the seq5(sequence of 5 items)
        //seq5Exec();
        //return;

        // short selftests
        //testGoalFullfillChain2_1();
        testAnticipationConfirm1();
        testAnticipationConfirm2();
        testTraceEmpty1();
        testGoalFullfill1();
        testGoalFullfill3(); // MSC patricks test
        testGoalFullfillIfSatisfied1();
        testGoalFullfillIfSatisfied2();

        Sys.println('... all unittests were successful!');


        var nExperimentThreads = 4; // number of threads for experiments


        var dbgCyclesVerbose = false; // debugging : are cycles verbose?

        var alien1RatioDist:IncrementalCentralDistribution = new IncrementalCentralDistribution();
        var pong2RatioDist:IncrementalCentralDistribution = new IncrementalCentralDistribution();
        var seaquest1RatioDist:IncrementalCentralDistribution = new IncrementalCentralDistribution();
        var seaquest1EnemySubDist:IncrementalCentralDistribution = new IncrementalCentralDistribution();


        // does run one experiment with the reasoner
        function doAlien1ExperimentWithExecutive(executive:Executive, cycles:Int) {
            executive.randomActProb = 0.12;
            
            var alien1 = new Alien1(executive);

            while(executive.cycle < cycles) {
                if(dbgCyclesVerbose) Sys.println('cycl=${executive.cycle}');
                
                // debug anticipations in flight
                var dbgAnticipationsInflight = false;
                if(dbgAnticipationsInflight && executive.anticipationsInflight.length > 0) {
                    Sys.println('');
                    Sys.println('ANTICIPATION inflight:');
                    for(iAif in executive.anticipationsInflight) {
                        Sys.println('   ${iAif.origin.convToStr()}  deadline=${iAif.deadline}');
                    }
                }

                var state:Array<Term> = alien1.emitState();
                if(dbgCyclesVerbose) Sys.println('cycl=${executive.cycle}  state=${alien1.stateAsStr}');
                executive.step(state);
            }

            // debug all evidence
            Logger.log('');
            for(iEvidence in executive.mem.pairs) {
                Logger.log(iEvidence.convToStr());
            }

            // add hit ratio to distribution
            alien1RatioDist.next(alien1.cntAliensHit / alien1.cntShoots);

            // print statistics of world:
            alien1.printStats();
        }

        // does run one experiment with the reasoner
        function doPong2ExperimentWithExecutive(executive:Executive, cycles:Int) {
            executive.randomActProb = 0.08;
            
            var pong2 = new Pong2(executive);

            while(executive.cycle < cycles) {
                if(dbgCyclesVerbose) Sys.println('cycl=${executive.cycle}');
                
                // debug anticipations in flight
                var dbgAnticipationsInflight = false;
                if(dbgAnticipationsInflight && executive.anticipationsInflight.length > 0) {
                    Sys.println('');
                    Sys.println('ANTICIPATION inflight:');
                    for(iAif in executive.anticipationsInflight) {
                        Sys.println('   ${iAif.origin.convToStr()}  deadline=${iAif.deadline}');
                    }
                }


                var state:Array<Term> = pong2.emitState();
                if(dbgCyclesVerbose) Sys.println('cycl=${executive.cycle}  state=${pong2.stateAsStr}');
                executive.step(state);
                pong2.simulate();
            }

            // debug all evidence
            Logger.log('');
            for(iEvidence in executive.mem.pairs) {
                Logger.log(iEvidence.convToStr());
            }

            // add hit ratio to distribution
            pong2RatioDist.next(pong2.hits / pong2.misses);

            // print statistics of world:
            pong2.printStats();
        }


        function doSeaquestExperimentWithExecutive(executive:Executive, cycles:Int) {
            executive.randomActProb = 0.04;
            
            var seaquest = new Seaquest1(executive);

            while(executive.cycle < cycles) {
                if(dbgCyclesVerbose) Sys.println('cycl=${executive.cycle}');
                
                // debug anticipations in flight
                var dbgAnticipationsInflight = false;
                if(dbgAnticipationsInflight && executive.anticipationsInflight.length > 0) {
                    Sys.println('');
                    Sys.println('ANTICIPATION inflight:');
                    for(iAif in executive.anticipationsInflight) {
                        Sys.println('   ${iAif.origin.convToStr()}  deadline=${iAif.deadline}');
                    }
                }

                if(false && executive.cycle % 15 == 0) { // do we interactivly debug seaquest?
                    seaquest.consoleVis();
                    Sys.sleep(0.03);
                }


                var state:Array<Term> = seaquest.emitState();
                if(dbgCyclesVerbose) Sys.println('cycl=${executive.cycle}  state=${seaquest.stateAsStr}');
                executive.step(state);
                seaquest.simulate();
            }

            // debug all evidence
            Logger.log('');
            for(iEvidence in executive.mem.pairs) {
                Logger.log(iEvidence.convToStr());
            }

            // add hit ratio to distribution
            seaquest1RatioDist.next(seaquest.cntEnemyHit / seaquest.cntShoots);
            seaquest1EnemySubDist.next(seaquest.cntEnemyHit);

            // print statistics of world:
            seaquest.printStats();
        }

        //trace(Par.checkSubset(new Par([new Term("a")]), new Par([new Term("a")])));

        var numberOfExperiments = 10;

        var nActiveExperimentThreads = 0; // how many threads are active for the experiment?
        var nActiveExperimentThreadsLock:sys.thread.Mutex = new sys.thread.Mutex();

        var numberOfDoneExperiments = 0; // how many experiments were done until now?

        // do experiments with executive/reasoner
        while(numberOfDoneExperiments < numberOfExperiments) {
            // wait as long as there are no available workthreads
            
            /*
            while(true) {
                nActiveExperimentThreadsLock.acquire();
                var activeThreads:Int = nActiveExperimentThreads;
                nActiveExperimentThreadsLock.release();
                
                if (activeThreads < nExperimentThreads) {
                    break;
                }
                
                Sys.sleep(0.08);
            }
            */
            
            nActiveExperimentThreadsLock.acquire();
            if (nActiveExperimentThreads >= nExperimentThreads) {
                nActiveExperimentThreadsLock.release();
                continue; // retry
            }
            nActiveExperimentThreadsLock.release();

            Sys.println('start thread  nactive=${nActiveExperimentThreads}');

            nActiveExperimentThreadsLock.acquire();
            nActiveExperimentThreads++;
            nActiveExperimentThreadsLock.release();

            #if (target.threaded)
            sys.thread.Thread.create(() -> {      
                var cyclesAlien2:Int = 30000;          
                var cyclesPong2:Int = 5*35001;//150000;
                var executive:Executive = new Executive();
                //doAlien1ExperimentWithExecutive(executive, cyclesAlien2);
                var executive:Executive = new Executive();
                doPong2ExperimentWithExecutive(executive, cyclesPong2);
                var executive:Executive = new Executive();
                //doSeaquestExperimentWithExecutive(executive, 30000);
                
                numberOfDoneExperiments++; // bump counter

                nActiveExperimentThreadsLock.acquire();
                nActiveExperimentThreads--;
                nActiveExperimentThreadsLock.release();

                Sys.println('alien1 hit ratio mean=${alien1RatioDist.mean} variance=${alien1RatioDist.calcVariance()} n=${alien1RatioDist.n}');
                Sys.println('pong2 ratio mean=${pong2RatioDist.mean} variance=${pong2RatioDist.calcVariance()} n=${pong2RatioDist.n}');
            });
            #end
        }


        Sys.println('alien1 hit ratio mean=${alien1RatioDist.mean} variance=${alien1RatioDist.calcVariance()} n=${alien1RatioDist.n}');
        Sys.println('pong2 ratio mean=${pong2RatioDist.mean} variance=${pong2RatioDist.calcVariance()} n=${pong2RatioDist.n}');
        Sys.println('seaquest1 enemy sub shot mean=${seaquest1EnemySubDist.mean} variance=${seaquest1EnemySubDist.calcVariance()} n=${seaquest1EnemySubDist.n}');
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

// injects a term on call
class TermInjOp extends Act {
    public var uut:Executive;
    public var term:Term;
    public var counter:Int = 0;
    public var queue:Array<Term> = [];

    public function new(name:String, uut, term) {
        super(name);
        this.uut = uut;
        this.term = term;
    }

    public override function exec(args:Array<Term>) {
        queue.push(TermUtils.cloneShallow(term));
        counter++;
    }
}




// action for the world
class Pong1Act extends Act {
    public var w:Pong1;
    public var delta:Float;

    public function new(name:String, w:Pong1, delta:Float) {
        super(name);
        this.delta = delta;
        this.w = w;
    }

    public override function exec(args:Array<Term>) {
        w.posX += delta;
        w.posX = Math.max(0.0, w.posX);
        w.posX = Math.min(1.0, w.posX);
    }
}

// pong world where the bat moves only when a action is done
class Pong1 {
    public var posX:Float = 0.35; // position of the agent
    public var posAlien:Float = 0.5; // position of the alien
    
    public var executive:Executive;

    public var stateAsStr:String = ""; // current state as string for debugging

    public function new(executive) {
        this.executive = executive;
        this.executive.acts.push({mass:1.0, act:new Pong1Act("^l", this, -0.1)});
        this.executive.acts.push({mass:1.0, act:new Pong1Act("^r", this, 0.1)});

        this.executive.goalSystem.eternalGoals.push(Term.Name("c")); // try to keep in center
    }

    // returns the state of the world
    public function emitState(): Array<Term> {
        var res = [];

        var diff: Float = posX - posAlien;
        if (Math.abs(diff) < 0.1) {
            stateAsStr = "c";
            res.push(Term.Name("c"));
        }
        else if(diff > 0.0) {
            stateAsStr = "r";
            res.push(Term.Name("r"));
        }
        else {
            stateAsStr = "l";
            res.push(Term.Name("l"));
        }

        return res;
    }
}





// action for the world
class Pong2Act extends Act {
    public var w:Pong2;
    public var delta:Float;

    public function new(name:String, w:Pong2, delta:Float) {
        super(name);
        this.delta = delta;
        this.w = w;
    }

    public override function exec(args:Array<Term>) {
        w.speed = delta;
    }
}


// pong world where the bat moves continiously and stop is available
class Pong2 {
    public var batPosX:Float = 0.35; // position of the agent
    public var speed:Float = 0.0; // speed of the bat
    

    public var posBallX:Float = 0.5; // position of the alien
    public var posBallY:Float = 0.5; // position of the alien
    public var velBallX:Float = 0.034;
    public var velBallY:Float = 0.04;
    

    public var executive:Executive;

    public var stateAsStr:String = ""; // current state as string for debugging

    public var misses = 0;
    public var hits = 0;

    public var isGood = false;

    public function new(executive) {
        this.executive = executive;
        this.executive.acts.push({mass:1.0, act:new Pong2Act("^l", this, -0.05)});
        this.executive.acts.push({mass:1.0, act:new Pong2Act("^r", this, 0.05)});
        this.executive.acts.push({mass:1.0, act:new Pong2Act("^stop", this, 0.0)});

        this.executive.goalSystem.eternalGoals.push(Term.Name("g")); // try to keep in center
    }

    // print statistics
    public function printStats() {
        Sys.println('pong2 misses = $misses');
        Sys.println('pong2 hits = $hits');
        Sys.println('hit ratio = ${hits / misses}');
    }

    // returns the state of the world
    public function emitState(): Array<Term> {
        var res = [];

        stateAsStr = "";

        var diff: Float = posBallX - batPosX;
        if (Math.abs(diff) < 0.1) {
            stateAsStr = "c";
            res.push(Term.Name("c"));
        }
        else if(diff > 0.0) {
            stateAsStr = "r";
            res.push(Term.Name("r"));
        }
        else if(diff < 0.0){
            stateAsStr = "l";
            res.push(Term.Name("l"));
        }

        if (isGood) {
            stateAsStr += " g";
            res.push(Term.Name("g"));
        }

        return res;
    }

    // simulates world
    public function simulate() {
        isGood = false;

        batPosX += speed;
        batPosX = Math.max(0.0, batPosX);
        batPosX = Math.min(1.0, batPosX);

        posBallX += velBallX;
        posBallY += velBallY;

        //trace('pong2 pos = <$posBallX, $posBallY>');

        if (posBallY < 0.0) {
            var diff: Float = posBallX - batPosX;
            var hitBat = Math.abs(diff) < 0.1;
            if (hitBat) {
                hits++;
            }
            else {
                misses++;
            }

            if (hitBat) {
                isGood = true;

                velBallY = Math.abs(velBallY);
            }
            else {
                // respawn ball
                posBallX = Math.random();
                posBallY = Math.random();

                velBallX = (Math.random() * 2.0 - 1.0) * 0.05;
                velBallY = (Math.random() * 2.0 - 1.0) * 0.05;
            }
        }

        if (posBallY > 1.0) {
            velBallY = -Math.abs(velBallY);
        }

        if (posBallX < 0.0) {
            velBallX = Math.abs(velBallX);
        }
        else if(posBallX > 1.0) {
            velBallX = -Math.abs(velBallX);
        }
    }
}





// action for the world
class Alien1Act extends Act {
    public var w:Alien1;
    public var delta:Float;

    public function new(name:String, w:Alien1, delta:Float) {
        super(name);
        this.delta = delta;
        this.w = w;
    }

    public override function exec(args:Array<Term>) {
        w.posX += delta;
        w.posX = Math.max(0.0, w.posX);
        w.posX = Math.min(1.0, w.posX);

        if (this.name == "^s") { // is shoot action?
            w.cntShoots++; // bump statistics

            for(idx in 0...w.posAliens.length) {
                var diff: Float = w.posX - w.posAliens[idx];
                if (Math.abs(diff) < 0.06*1.5) { // did we hit a alien?
                    w.state.push(Term.Name('s$idx')); // shot down
                    w.posAliens[idx] = Math.random(); // respawn at random position

                    w.cntAliensHit++; // bump statistics
                    break; // break because the shot was absorbed by one alien and can't hit another
                }
            }
        }
    }
}

// alien invasion world where aliens move around and where the player can move only incrementally
class Alien1 {
    public var posX:Float = 0.35; // position of the agent

    public var posAliens:Array<Float> = [0.5, 0.7]; // position of the aliens
    
    public var executive:Executive;

    public var stateAsStr:String = ""; // current state as string for debugging

    public var state:Array<Term> = [];

    public var cntShoots:Int = 0; // statistics - how many shots were fired
    public var cntAliensHit:Int = 0; // statistics - how many aliens were hit by shots

    // print statistics
    public function printStats() {
        Sys.println('shots fired = $cntShoots');
        Sys.println('aliens hit = $cntAliensHit');
        Sys.println('hit ratio = ${cntAliensHit / cntShoots}');
    }

    public function new(executive) {
        this.executive = executive;
        this.executive.acts.push({mass:1.0, act:new Alien1Act("^l", this, -0.06)});
        this.executive.acts.push({mass:1.0, act:new Alien1Act("^r", this, 0.06)});
        {
            var shootAct = new Alien1Act("^s", this, 0.0);
            shootAct.refractoryPeriod = 4; // don't let the agent spam the shot button
            this.executive.acts.push({mass:1.0, act:shootAct});
        }

        this.executive.goalSystem.eternalGoals.push(Term.Name("s0")); // shoot down
        this.executive.goalSystem.eternalGoals.push(Term.Name("s1")); // shoot down
    }

    // returns the state of the world
    public function emitState(): Array<Term> {
        var res = state;

        stateAsStr = "";

        for(idx in 0...posAliens.length) {
            var diff: Float = posX - posAliens[idx];
            if (Math.abs(diff) < 0.1) {
                stateAsStr += ' c$idx';
                res.push(Term.Name('c$idx'));
            }
            else if(diff > 0.0) {
                stateAsStr += ' r$idx';
                res.push(Term.Name('r$idx'));
            }
            else {
                stateAsStr += ' l$idx';
                res.push(Term.Name('l$idx'));
            }
        }

        state = [];
        return res;
    }
}











class Seaquest1Act extends Act {
    public var w:Seaquest1;
    public var deltaX:Float;
    public var deltaY:Float;

    public function new(name:String, w:Seaquest1, deltaX:Float, deltaY:Float) {
        super(name);
        this.deltaX = deltaX;
        this.deltaY = deltaY;
        this.w = w;
    }

    public override function exec(args:Array<Term>) {
        w.posX += deltaX;
        w.posY += deltaY;
        w.posX = Math.max(0.0, w.posX);
        w.posX = Math.min(1.0, w.posX);
        w.posY = Math.max(0.0, w.posY);
        w.posY = Math.min(1.0, w.posY);


        if (this.name == "^s") { // is shoot action?
            w.cntShoots++; // bump statistics
            w.actShoot = true;
        }

        if (this.name == "^l") {
            w.dir = -1;
        }
        else if(this.name == "^r") {
            w.dir = 1;
        }
    }
}

class Entity {
    public var type:String;
    public var posX:Float = 0.0;
    public var posY:Float = 0.0;
    public var velX:Float = 0.0;
    public var velY:Float = 0.0;
    
    public function new(type) {
        this.type=type;
    }

    public function step() {
        posX+=velX;
        posY+=velY;
    }
}

// TODO< add direction of submarine and change it when ever ^r,^l is done, also propagate it as state to reasoner >
class Seaquest1 {
    public var posX:Float = 0.35; // position of the agent
    public var posY:Float = 0.5; // position of the agent
    public var dir:Int = 1; // "look" direction of submarine

    public var actShoot:Bool = false; // shoot in the next timestep?

    public var entities:Array<Entity> = [];

    public var executive:Executive;

    public var stateAsStr:String = ""; // current state as string for debugging

    public var state:Array<Term> = [];

    public var cntShoots:Int = 0; // statistics - how many shots were fired
    public var cntEnemyHit:Int = 0; // statistics - how many enemy submarines were hit
    public var cntFishHit:Int = 0; // statistics - how many enemy fishes were hit
    

    // print statistics
    public function printStats() {
        Sys.println('shots fired = $cntShoots');
        Sys.println('enemy hit = $cntEnemyHit');
        Sys.println('hit ratio = ${cntEnemyHit / cntShoots}');
    }

    public function new(executive) {
        this.executive = executive;
        this.executive.acts.push({mass:0.25, act:new Seaquest1Act("^l", this, -0.06, 0.0)});
        this.executive.acts.push({mass:0.25, act:new Seaquest1Act("^r", this, 0.06, 0.0)});
        this.executive.acts.push({mass:0.25, act:new Seaquest1Act("^u", this, 0.0, -0.06)});
        this.executive.acts.push({mass:0.25, act:new Seaquest1Act("^d", this, 0.0, 0.06)});
        {
            var shootAct = new Seaquest1Act("^s", this, 0.0, 0.0);
            shootAct.refractoryPeriod = 8; // don't let the agent spam the shot button
            this.executive.acts.push({mass:1.0, act:shootAct});
        }

        this.executive.goalSystem.eternalGoals.push(Term.Name("s0")); // shoot down
        this.executive.goalSystem.eternalGoals.push(Term.Name("s1")); // shoot down
    }

    // returns the state of the world
    public function emitState(): Array<Term> {
        var res = state;

        stateAsStr = "";

        {
            var eSubs = entities.filter(e -> e.type == "S"); // filter for enemy submarines
            for(idx in 0...eSubs.length) {
                var diffX:Float = posX - eSubs[idx].posX;
                var diffY:Float = posY - eSubs[idx].posY;
                
                var enc:String = "";
                if (Math.abs(diffX) < 0.1) {
                    enc += 'c';
                }
                else if(diffX > 0.0) {
                    enc += 'r';
                }
                else {
                    enc += 'l';
                }

                if (Math.abs(diffY) < 0.1) {
                    enc += 'c';
                }
                else if(diffY > 0.0) {
                    enc += 'b'; // below
                }
                else {
                    enc += 'a';
                }

                var dirAsTerm = dir == 1 ? "p" : "n";

                stateAsStr += ' S$dirAsTerm$enc$idx';
                res.push(Term.Name('S$dirAsTerm$enc$idx'));
            }
        }

        state = [];
        return res;
    }

    // simulates world
    public function simulate() {
        if (actShoot) {
            // spawn projectile
            var spawnedProj = new Entity("p");
            entities.push(spawnedProj);
            spawnedProj.velX = 0.02 * dir;
            spawnedProj.posX = posX;
            spawnedProj.posY = posY;
        }
        actShoot = false;

        // debug state of world
        //for(ie in entities.filter(ie -> ie.type == "S")) { // for all submarines
        //    Sys.println('seaquest state  enemy <${ie.posX},${ie.posY}>');
        //}

        for(simStep in 0...5) {
            for(ie in entities) {
                ie.step();
            }

            // check collision between projectile and enemy
            {
                var noSubs = entities.filter(ie -> ie.type != "S");
                var subs = entities.filter(ie -> ie.type == "S");
                var nSubsBefore = subs.length;

                var subs2 = [];
                var subIdx=0;
                for(ie in subs) {
                    var hit = false;
                    for(ip in entities.filter(ie -> ie.type == "p")) {
                        var diffX = Math.abs(ip.posX - ie.posX);
                        var diffY = Math.abs(ip.posY - ie.posY);
                        hit = hit || (diffX < 0.1 && diffY < 0.1);
                    }

                    if (hit) {
                        //Sys.println('seaquest  enemy hit!');

                        state.push(Term.Name('s$subIdx')); // shot down

                        cntEnemyHit++; // bump counter
                    }

                    if (!hit) {
                        subs2.push(ie); // add sub if it wasn't hit
                    }

                    subIdx++;
                }

                entities = noSubs.concat(subs2);
            }
        }



        { // remove entities which are out of bound
            entities = entities.filter(ie -> {
                return ie.posX >= 0.0 && ie.posX <= 1.0; // else projectile must be in screen
            });
        }

        // respawn submarine if it is not present anymore
        var nSubmarines = entities.filter(ie -> ie.type == "S").length;
        if (nSubmarines < 1) {
            //Sys.println("seaquest: respawn enemy");

            var spawnedSub = new Entity("S");

            var dirX:Int = Std.random(2) == 0 ? -1 : 1;
            spawnedSub.posX = (dirX == 1 ? 0.1 : 1.0-0.1);
            spawnedSub.posY = Math.random();
            spawnedSub.velX = 0.01 * dirX;
            entities.push(spawnedSub);
        }
    }

    // display console visualization
    public function consoleVis() {
        var lines=[];
        for(i in 0...12) {
            lines.push([for (i in 0...15) " "]);
        }

        function visu(x:Float, y:Float, sign:String) {
            if (x < 0.0 || x > 1.0 || y < 0.0 || y>1.0) {
                return;
            }
            lines[Std.int(y * 10)][Std.int(x * 10)] = sign;
        }

        visu(posX, posY, "X");

        var submarines = entities.filter(ie -> ie.type == "S");
        for(is in submarines) {
            visu(is.posX, is.posY, "S");
        }


        var projectiles = entities.filter(ie -> ie.type == "p");
        for(is in projectiles) {
            visu(is.posX, is.posY, "p");
        }

        for(j in lines) {
            Sys.println(j.join(""));
        }

        Sys.println('shots fired = $cntShoots');
        Sys.println('enemy hit = $cntEnemyHit');
        Sys.println('hit ratio = ${cntEnemyHit / cntShoots}');
    }

}









//class Revenge1Op extends Act {
//    public var opname = "^lu"; // ladder up
//}

// TODO< implement functionality of ops >

// ^lu : ladder up
// ^ld : ladder down

// ^l : left
// ^r : right

// a simple version of Montezuma's Revenge
class MontezumaRevenge1 {
    public var posX = 4;
    public var posY = 1;

    // w : walkkable
    // l : ladder
    public var map = [
        "wwwwlwwww",
        "    l    ",
        "    l    ",
        "wwwwlwwww"
    ];

    public function isOnLadder() {
        return map[posY].charAt(posX) == 'l'; // is on ladder if symbol is 'l' which stands for ladder
    }

    public function canClimbUpDOwnOnLadder() {
        return isOnLadder(); // can climb up or down if it is on ladder
    }

    public function retStateName() {
        if (isOnLadder()) {
            return 'l_${posX}_${posY}'; // ladder
        }
        return '${posX}_${posY}';
    }

    // state transition functionality
    // try to go into direction "l" or "r"
    public function tryDir(dir:String) {
        if (isOnLadder() && dir == "l" && map[posY].charAt(posX-1) == 'w') { // is left op and is left walkable?
            posX--;
        }
        else if (isOnLadder() && dir == "r" && map[posY].charAt(posX+1) == 'w') { // is left op and is left walkable?
            posX++;
        }
        else if (!isOnLadder() && dir == "l" && map[posY].charAt(posX-1) != ' ') { // is left op and is left walkable?
            posX--;
        }
        else if (!isOnLadder() && dir == "r" && map[posY].charAt(posX+1) != ' ') { // is left op and is left walkable?
            posX++;
        }
    }


}
