import haxe.Int64;

// decision making experiment

// features:
// * anticipation
// * decision making: actions can have a refractory peroid to avoid spamming the environment with pointless actions
// * goal system: expectation and tree based goal system

class ExpDescn2 {

    
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
        uut.step([Term.Name("^b")]);
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
            pair.cond = new Par([Term.Name("b")]);
            pair.act = [Term.Name("^x")];
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
        uut.step([Term.Name("^x")]);
        uut.step([Term.Name("b")]);

        // flood sequence out of memory
        for(i in 0...50) {
            uut.step([]);
        }

        uut.step([Term.Name("b")]);
        uut.step([Term.Name("^y")]);
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

        for(t in 0...1000) {
            uut.step([]);
        }

        // debug all evidence
        Sys.println('');
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
            pair.cond = new Par([Term.Name("b")]);
            pair.act = [Term.Name("^x")];
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
            pair.cond = new Par([Term.Name("a")]);
            pair.act = [Term.Name("^x")];
            pair.effect = new Par([Term.Name("b")]);
            uut.mem.pairs.push(pair);

        }

        {
            var pair = new Pair(uut.createStamp());
            pair.cond = new Par([Term.Name("b")]);
            pair.act = [Term.Name("^x")];
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
        uut.step([Term.Name("^a")]);
        uut.step([Term.Name("b")]);

        // flood sequence out of memory
        for(i in 0...50) {
            uut.step([]);
        }

        uut.step([Term.Name("b")]);
        uut.step([Term.Name("^b")]);
        uut.step([Term.Name("c")]);

        // flood sequence out of memory
        for(i in 0...50) {
            uut.step([]);
        }

        uut.step([Term.Name("c")]);
        uut.step([Term.Name("^c")]);
        uut.step([Term.Name("d")]);

        // flood sequence out of memory
        for(i in 0...50) {
            uut.step([]);
        }

        uut.step([Term.Name("d")]);
        uut.step([Term.Name("^d")]);
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

    public static function main() {
        // short selftests
        testGoalFullfillChain2_1();

        return;

        testAnticipationConfirm1();
        testAnticipationConfirm2();
        testTraceEmpty1();
        testGoalFullfill1();
        testGoalFullfill3(); // MSC patricks test
        testGoalFullfillIfSatisfied1();
        testGoalFullfillIfSatisfied2();


        var nExperimentThreads = 3; // number of threads for experiments


        var dbgCyclesVerbose = true; // debugging : are cycles verbose?

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
            Sys.println('');
            for(iEvidence in executive.mem.pairs) {
                Sys.println(iEvidence.convToStr());
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
            Sys.println('');
            for(iEvidence in executive.mem.pairs) {
                Sys.println(iEvidence.convToStr());
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

                if(false) { // do we interactivly debug seaquest?
                    seaquest.consoleVis();
                    Sys.sleep(0.03);
                }


                var state:Array<Term> = seaquest.emitState();
                if(dbgCyclesVerbose) Sys.println('cycl=${executive.cycle}  state=${seaquest.stateAsStr}');
                executive.step(state);
                seaquest.simulate();
            }

            // debug all evidence
            Sys.println('');
            for(iEvidence in executive.mem.pairs) {
                Sys.println(iEvidence.convToStr());
            }

            // add hit ratio to distribution
            seaquest1RatioDist.next(seaquest.cntEnemyHit / seaquest.cntShoots);
            seaquest1EnemySubDist.next(seaquest.cntEnemyHit);

            // print statistics of world:
            seaquest.printStats();
        }

        //trace(Par.checkSubset(new Par([new Term("a")]), new Par([new Term("a")])));

        var numberOfExperiments = 20;

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
                doAlien1ExperimentWithExecutive(executive, cyclesAlien2);
                doPong2ExperimentWithExecutive(executive, cyclesPong2);
                doSeaquestExperimentWithExecutive(executive, 30000);
                
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


// lookup table of a type by condition of a pair
// supports query by subset
@:generic
class ByCond<Type> {

    // maps conditions to the pairs which contain the condition
    // key is the string serialization of the parallel key terms as a string
    private var pairsByCond:Map<String,Array<Type>> = new Map<String,Array<Type>>();

    public function new() {}

    public function add(events:Array<Term>, value:Type) {
        { // store by cond
            {
                var keyComplete = ""+events.map(v -> TermUtils.convToStr(v));
                var tableResult = pairsByCond.get(keyComplete);
                if (tableResult != null) {
                    var arr = tableResult.concat([value]);
                    pairsByCond.set(keyComplete, arr);
                }
                else {
                    pairsByCond.set(keyComplete, [value]);
                }
            }

            for(iEvent in events) {
                var key = ""+[TermUtils.convToStr(iEvent)];
                var tableResult = pairsByCond.get(key);
                if (tableResult != null) {
                    var arr = tableResult.concat([value]);
                    pairsByCond.set(key, arr);
                }
                else {
                    pairsByCond.set(key, [value]);
                }
            }
        }
    }

    public function queryByCond(parEvents:Array<Term>): Array<Type> {
        //Par.checkSubset(new Par(parEvents), v.cond)

        var result = [];

        {
            var keyComplete = ""+parEvents.map(v -> TermUtils.convToStr(v));
            var tableResult = pairsByCond.get(keyComplete);
            if (tableResult != null) {
                result = result.concat(tableResult);
            }
        }

        for(iEvent in parEvents) {
            var key = ""+[TermUtils.convToStr(iEvent)];
            var tableResult = pairsByCond.get(key);
            if (tableResult != null) {
                result = result.concat(tableResult);
            }
        }

        return result;
    }
}



class Memory {
    public var pairs:Array<Pair> = []; // all known pairs, read only!
    // is extremely slow to iterate on!

    // maps conditions to the pairs which contain the condition
    // key is the string serialization of the parallel key terms as a string
    private var byCond:ByCond<Pair> = new ByCond<Pair>(); //:Map<String,Array<Pair>> = new Map<String,Array<Pair>>();

    public function new() {}

    public function addPair(pair:Pair) {
        pairs.push(pair);

        byCond.add(pair.cond.events, pair);
    }

    // queries by conditional, either the complete parEvents or for single events (subset)
    public function queryPairsByCond(parEvents:Array<Term>): Array<Pair> {
        return byCond.queryByCond(parEvents);
    }
}

class Executive {
    
    //commented because it is in memory    public var pairs:Array<Pair> = []; // all known pairs

    public var acts:Array<{mass:Float, act:Act}> = []; // list of all actions
    
    public function new() {
        var traceLength:Int = 10; // the trace
        for(i in 0...traceLength) {
            trace.push(new Par([]));
        }
    }

    var queuedAct: String = null;
    var queuedActOrigin: Pair = null; // origin of the queued action if it was done by the executive

    var trace:Array<Par> = [];

    public var randomActProb:Float = 0.0; // config - propability to do random action

    public var decisionThreshold:Float = 0.6; // config

    public var anticipationDeadline = 20; // config - anticipation deadline in cycles


    public var cycle:Int = 0; // global cycle timer

    public var rng:Rule30Rng = new Rule30Rng();


    public var dbgEvidence = false; // debugging - debug new and revised evidence?
    public var dbgAnticipationVerbose = true; // are anticipations verbose?

    public var dbgDescisionMakingVerbose = false; // debugging : is decision making verbose
    public var dbgExecVerbose = true; // debugging : is execution of ops verbose?

    public var mem = new Memory();

    public function goalNow(g:Term) {
        // check and exec if it is a action
        if (TermUtils.isOp(g)) {
            var opName:String = switch(g) {
                case Name(n): n;
                default: null; // must not happen!
            }

            execAct(opName, null);
        }

        // record to trace
        this.trace[0].events.push(g);
    }

    public function step(parEvents:Array<Term>) {
        // * add evidence of parallel events
        //   builds a =|> b  b =|> a  from parEvents=[a, b]
        if (parEvents.length > 1) {
            // TODO< sample ba random if there are to many events >
            for(idxA in 0...parEvents.length) for(idxB in 0...parEvents.length) {
                addEvidence([parEvents[idxA]], [parEvents[idxB]], createStamp(), null, true);
                addEvidence([parEvents[idxB]], [parEvents[idxA]], createStamp(), null, true);
            }
        }

        // * try to confirm anticipations
        anticipationTryConfirm(parEvents);

        // * advance time by one step
        for(idx2 in 1...this.trace.length) {
            var idx = this.trace.length-1-idx2;
            this.trace[idx+1] = this.trace[idx];
        }
        this.trace[0] = new Par([]);
        this.trace[0].events = parEvents;

        if (false) { // debug trace
            Sys.println('trace');
            for(idx2 in 0...this.trace.length) {
                var idx = this.trace.length-1-idx2;
                Sys.println(' [$idx]  ${this.trace[idx].events.map(v -> TermUtils.convToStr(v))}');
            }
        }

        { // do random action
            if(rng.nextFloat() < randomActProb && queuedAct == null) { // do random action
                if (true) Sys.println('random act');
                
                var possibleActs = acts.filter(iAct -> iAct.act.refractoryPeriodCooldown <= 0); // only actions which are cooled down are possible as candidates

                var mass:Float = 0.0;
                for(iPossibleAct in possibleActs) {
                    mass += iPossibleAct.mass;
                }

                var selMass = Math.random()*mass;

                var massAccu = 0.0;
                for(idx in 0...possibleActs.length) {
                    queuedAct = possibleActs[idx].act.name; // queue action as next action
                    queuedActOrigin = null; // has no origin because it was done by random

                    massAccu += possibleActs[idx].mass;
                    if (massAccu > selMass) {
                        break;
                    }
                }

                //commented because old code
                //var idx=Std.random(possibleActs.length);
                //queuedAct = possibleActs[idx].act.name; // queue action as next action
                //queuedActOrigin = null; // has no origin because it was done by random
            }
        }
        
        if (queuedAct != null) {
            execAct(queuedAct, queuedActOrigin);

            // record to trace
            this.trace[0].events.push(Term.Name(queuedAct));
        }

        if (false) { // debug trace
            Sys.println('trace after queue insert');
            for(idx2 in 0...this.trace.length) {
                var idx = this.trace.length-1-idx2;
                Sys.println(' [$idx]  ${this.trace[idx].events.map(v -> TermUtils.convToStr(v))}');
            }
        }

        
        

        // * decision making
        queuedAct = null;
        queuedActOrigin = null;
        var bestDecisionMakingCandidate:Pair;
        { // select best decision making candidate
            
            var timeBefore = Sys.time();
            
            
            var candidates:Array<Pair> = [];// candidates for decision making in this step
            // * compute candidates for decision making in this step
            candidates = mem.queryPairsByCond(parEvents)
                .filter(iPair -> iPair.effect.events.filter(iEvent -> goalSystem.isEternalGoal(iEvent)).length > 0) // does it have a eternal goal as a effect?
                .filter(v -> !v.isConcurrentImpl); /////pairs.filter(v -> Par.checkSubset(new Par(parEvents), v.cond));
            
            // (&/, a, ^op) =/> b  where b!
            var candidatesByLocalChainedGoal: Array<{pair:Pair, exp:Float}> = [
                for (iPair in candidates) {pair:iPair, exp:Tv.calcExp(iPair.calcFreq(), iPair.calcConf())}
            ];
            
            //commented because it is to slow
            //candidatesByLocalChainedGoal = filterCandidatesByGoal(candidates); // chain local pair -> matching goal in goal system
            
            var timeBefore2 = Sys.time();
            var candidatesByGoal: Array<{pair:Pair, exp:Float}> = goalSystem.retDecisionMakingCandidatesForCurrentEvents(parEvents);
            if(dbgDescisionMakingVerbose) Sys.println('descnMaking goal system time=${Sys.time()-timeBefore2}');

            var timeBefore3 = Sys.time();
            var candidatesFromForwardChainer1 = ForwardChainer.step(parEvents, 1, this);
            var candidatesFromForwardChainer2 = ForwardChainer.step(parEvents, 2, this);
            if(dbgDescisionMakingVerbose) Sys.println('descnMaking goal system forward chainer time=${Sys.time()-timeBefore3}');

            var candidates: Array<{pair:Pair, exp:Float}> = candidatesByLocalChainedGoal
                .concat(candidatesByGoal)
                .concat(candidatesFromForwardChainer1)
                .concat(candidatesFromForwardChainer2);
            bestDecisionMakingCandidate = selBestAct(candidates);

            var timeRequired = Sys.time()-timeBefore;

            if(dbgDescisionMakingVerbose) Sys.println('descnMaking time=$timeRequired');
        }
        if (bestDecisionMakingCandidate != null) {
            var bestDecisionExp:Float = Tv.calcExp(bestDecisionMakingCandidate.calcFreq(), bestDecisionMakingCandidate.calcConf());
            
            if (dbgDescisionMakingVerbose) trace('decsn making $bestDecisionExp > $decisionThreshold');
            
            // helper function to return name
            function retName(t:Term):String {
                return switch(t) {
                    case Name(n): n;
                    default: throw "Invalid name!";
                }
            }

            if (
                bestDecisionExp > decisionThreshold && 
                retActByName(retName(bestDecisionMakingCandidate.act[0])).refractoryPeriodCooldown <= 0 // is it possible to execute the action based on refractory period?
            ) {
                queuedAct = retName(bestDecisionMakingCandidate.act[0]); // queue action for next timestep
                queuedActOrigin = bestDecisionMakingCandidate;
            }
        }
        

        // * store sequences if possible
        {
            

            // do terms contain a action?
            function containsAction(terms:Array<Term>): Bool {
                return terms.filter(v -> TermUtils.isOp(v)).length > 0;
            }

            // aren't terms only actions?
            function containsAnyNonaction(terms:Array<Term>): Bool {
                return terms.filter(v -> !TermUtils.isOp(v)).length > 0;
            }

            if (
                this.trace[0].events.length > 0 // most recent trace element must contain a event to get chained
            ) {

                // is any event of the most recent events a goal?
                var hasMostRecentEventGoal = parEvents.filter(iEvent -> goalSystem.isEternalGoal(iEvent)).length > 0;


                // function to scan through condition candidates up to "bounding" op-event
                // and to build (&/, a, ^b) =/> c
                //
                // /param scanAllConditions scan for all conditions and don't stop at the first?
                //        this is only advised for very important effects
                function scanBoundingEvntAndAddImplSeq(traceIdxOfOpEvent:Int, scanAllConditions:Bool) {
                    for(iConditionCandidateIdx in traceIdxOfOpEvent+1...this.trace.length) { // iterate over indices in trace for condition of impl seq we want to build
                        
                        // "break" sequence by another op
                        // because we only build (&/, a, ^b) =/> c, not some impl seq with two or more ops
                        if (containsAction(this.trace[iConditionCandidateIdx].events)) {
                            break;
                        }

                        if (!containsAnyNonaction(this.trace[iConditionCandidateIdx].events)) {
                            continue;
                        }


                        // build impl seq(s)
                        // because it has at least one (&/, events, ^action) =/> effect term
                
                        var nonactionsOf2:Array<Term> = this.trace[iConditionCandidateIdx].events.filter(v -> !TermUtils.isOp(v));
                        var actionsOf1:Array<Term> = this.trace[traceIdxOfOpEvent].events.filter(v -> TermUtils.isOp(v));
                        var nonactionsOf0:Array<Term> = this.trace[0].events.filter(v -> !TermUtils.isOp(v));
                        
                        {
                            for(iActionTerm in actionsOf1) { // iterate over all actions done at that time
                                if (dbgEvidence) {                            
                                    var stamp:Stamp = createStamp();
                                    var createdPair:Pair = new Pair(stamp);
                                    createdPair.cond = new Par(nonactionsOf2);
                                    createdPair.act = actionsOf1;
                                    createdPair.effect = new Par(nonactionsOf0);
                                    trace('evidence  ${createdPair.convToStr()}');
                                }
                                

                                var stamp:Stamp = createStamp();

                                addEvidence(nonactionsOf2, nonactionsOf0, stamp, iActionTerm, false);
                                
                                // add evidence of combinations of single events of cond and effect
                                if (nonactionsOf2.length > 1) {
                                    for(iCond in nonactionsOf2) {
                                        addEvidence([iCond], nonactionsOf0, stamp, iActionTerm, false);
                                    }
                                }

                                if (nonactionsOf0.length > 1) {
                                    for(iEffect in nonactionsOf0) {
                                        addEvidence(nonactionsOf2, [iEffect], stamp, iActionTerm, false);
                                    }
                                }
                                
                                if (nonactionsOf2.length > 1 && nonactionsOf0.length > 1) {
                                    for(iCond in nonactionsOf2) {
                                        for (iEffect in nonactionsOf0) {
                                            addEvidence([iCond], [iEffect], stamp, iActionTerm, false);
                                        }
                                    }
                                }
                            }
                        }


                        if (!scanAllConditions) {
                            break; // we break because else we may overwhelm the system with pointless derivations
                        }
                    }
                }

                // we need to build sequences of observations,
                // but we also have to be careful not to build to many
                //
                // so we need to scan the trace for a op which "connects" the event(s) before the op to the last event(s)

                
                for(idx in 1...this.trace.length-1) {
                    if (containsAction(this.trace[idx].events)) {
                        var traceIdxOfOpEvent = idx;



                        scanBoundingEvntAndAddImplSeq(traceIdxOfOpEvent, hasMostRecentEventGoal);

                        // we care about all possible impl seq if the most recent events contain goal
                        if (!hasMostRecentEventGoal) {
                            break; 
                        }
                    }
                }
            }
        }

        anticipationMaintainNegAnticipations();
        decisionmakingActionCooldown();
        goalSystem.step(this); // let the goal system manage eternal goals etc
        goalSystem.goalDerivation(this);

        cycle++; // advance global cycle timer
    }

    
    // adds new evidence
    // /param iActionTerm is the action term which is used for checking and, can be null if isConcurrentImpl is true
    private function addEvidence(conds:Array<Term>, effects:Array<Term>, stamp:Stamp, iActionTerm:Term, isConcurrentImpl) {
        
        if (Par.checkIntersect(new Par(conds), new Par(effects))) {
            return; // exclude (&/, a, ^b) =/> a
        }

        for(iPair in mem.queryPairsByCond(conds)) { // search for existing evidence and try to revise
            ////trace('cs ${Par.checkSubset(iPair.cond, new Par(conds))} ${iPair.cond.events.map(v ->v.content)} ${new Par(conds).events.map(v->v.content)}');
            
            if (
                iPair.isConcurrentImpl == isConcurrentImpl &&
                //iPair.act.length == 1 &&
                (isConcurrentImpl ? true : TermUtils.equal(iPair.act[0], iActionTerm)) &&
                Par.checkSubset(iPair.cond, new Par(conds)) // TODOOPTIMIZE< is not necessary >
            ) {
                // iPair.evidenceCnt++; // commented here because neg evidence should only come from neg-confirm, because we assume a open-world

                if (Par.checkSubset(iPair.effect, new Par(effects))) {
                    iPair.evidenceCnt++;
                    iPair.evidencePositive++;
                }
            }
        }

        var existsEvidence = false; // does exact evidence exist?
        for(iPair in mem.queryPairsByCond(conds)) { // search for exact evidence
            if (
                iPair.isConcurrentImpl == isConcurrentImpl &&
                //iPair.act.length == 1 &&
                (isConcurrentImpl ? true : TermUtils.equal(iPair.act[0], iActionTerm)) &&
                Par.checkSame(iPair.cond, new Par(conds)) // TODOOPTIMIZE< is not necessary >
            ) {
                if (Par.checkSame(iPair.effect, new Par(effects))) {
                    existsEvidence = true;
                }
            }
        }

        if (!existsEvidence) { // create new evidence if it doesn't yet exist
            
            // store pair
            var createdPair:Pair = new Pair(stamp);
            createdPair.cond = new Par(conds);
            createdPair.act = iActionTerm != null ? [iActionTerm] : [];
            createdPair.effect = new Par(effects);
            createdPair.isConcurrentImpl = isConcurrentImpl;

            if(dbgEvidence) trace('create new evidence ${createdPair.convToStr()}');

            mem.addPair(createdPair); ///pairs.push(createdPair);
        }
    }

    // decrements the remaining refractory period
    private function decisionmakingActionCooldown() {
        for (iAct in acts) {
            iAct.act.refractoryPeriodCooldown--;
        }
    }

    // emits neg-confirm if anticipation didn't occur
    private function anticipationMaintainNegAnticipations() {
        // checks if anticipations didn't occur till the deadline
        // emits a neg-confirm if this is the case

        var failedAnticipations = anticipationsInflight.filter(aif -> aif.deadline <= cycle);
        for(iFailedAnticipation in failedAnticipations) { // loop to emit neg-confirm
            if(dbgAnticipationVerbose) trace('ANTICIPATION failed ${iFailedAnticipation.origin.convToStr()}');
            iFailedAnticipation.origin.evidenceCnt++; // add neg evidence
        }

        anticipationsInflight = anticipationsInflight.filter(aif -> aif.deadline > cycle); // let not failed anticipations survive
    }
    
    // tries to confirm anticipations which are in-flight
    private function anticipationTryConfirm(parEvents:Array<Term>) {
        anticipationsInflight = anticipationsInflight.filter(aif -> !Par.checkSubset(new Par(parEvents), aif.origin.effect));
    }

    // filters all candidates by the active goals of the system
    function filterCandidatesByGoal(candidates:Array<Pair>):Array<{pair:Pair, exp:Float}> {
        var res = [];
        for(iCandi in candidates) {
            var add=false;

            // add it to the decision making candidates if it is a candidate
            var tv:Tv = goalSystem.retDecisionMakingCandidateTv(iCandi); 
            if (tv != null) {
                var exp = Tv.calcExp(tv.freq, tv.conf);
                res.push({pair:iCandi, exp:exp}); // add if it is a candidate if the effect of it is a goal
            }

            /* commented because it belonged to old goal system

            var sampledGoals = [];
            { // sample some goals
                var thisSampledGoal = goalSystem.sample(rng, cycle);
                if (thisSampledGoal != null) {
                    sampledGoals.push(thisSampledGoal);
                }
            }

            for(iGoal in sampledGoals) {
                for(iEffect in iCandi.effect.events) {
                    if (TermUtils.equal(iEffect, iGoal.term)) {
                        add = true;
                        break; // optimization
                    }
                }
            }

            if (add) {
                res.push({pair:iCandi, tv:tv});
            }
            */
        }

        return res;
    }

    function retActByName(actName:String): Act {
        return acts.filter(iAct -> iAct.act.name == actName)[0].act;
    }

    // realize action
    // /param origin origin of the action, used for anticipation , can be null
    function execAct(actName:String, origin:Pair) {
        if(dbgExecVerbose) Sys.println('ACT $actName origin = ${origin != null ? origin.convToStr() : "null"}');

        // lookup action and call handler
        var act = retActByName(actName);
        act.refractoryPeriodCooldown = act.refractoryPeriod;
        act.exec();

        if (origin != null) {
            // add anticipation
            if(dbgAnticipationVerbose) trace('ANTICIPATION anticipate ${origin.convToStr()}');
            anticipationsInflight.push(new InflightAnticipation(origin, cycle + anticipationDeadline));
        }
    }

    // select best action
    public function selBestAct(candidates:Array<{pair:Pair, exp:Float}>): Pair {
        if (dbgDescisionMakingVerbose) trace('selBestAct() #candidates=${candidates.length}');

        if (candidates.length == 0) {
            return null; // no action
        }

        var bestExp:Float = candidates[0].exp;
        var bestCandidate = candidates[0].pair;

        for(iCandidate in candidates) {
            if (iCandidate.exp > bestExp) {
                bestExp = iCandidate.exp;
                bestCandidate = iCandidate.pair;
            }
        }

        if (dbgDescisionMakingVerbose) trace('FOUND best act candidate ${bestCandidate.convToStr()}');

        return bestCandidate;
    }

    // helper to create stamp
    public function createStamp():Stamp {
        return new Stamp([Int64.make(0, stampCounter++)], new StructuralOriginsStamp([]));
    }

    public var anticipationsInflight:Array<InflightAnticipation> = []; // anticipations in flight

    public var goalSystem:AbstractGoalSystem = new TreePlanningGoalSystem();

    // TODO< should be Int64 >
    public var stampCounter:Int = 1; // counter for the creation of new stamps
}


class AbstractGoalSystem {
    public var eternalGoals:Array<Term> = []; // list of all eternal goals which have to get pursued by the system

    public function new() {}

    // try to add a derived goal if it doesn't exist already
    // /param time absolute executive reasoner time in cycles
    //public function tryAddDerivedGoal(term:Term, tv:Tv, stamp:Stamp, time:Int) {
    //    throw "VIRTUAL METHOD CALLED";
    //}

    public function step(executive:Executive) {
        throw "VIRTUAL METHOD CALLED";
    }

    public function goalDerivation(executive:Executive) {
        throw "VIRTUAL METHOD CALLED";
    }

    // sample a goal based on probability distribution
    public function sample(rng:Rule30Rng, time:Int): ActiveGoal {
        throw "VIRTUAL METHOD CALLED";
    }

    public function retNoneternalGoals(executive:Executive): Array<ActiveGoal> {
        throw "VIRTUAL METHOD CALLED";
    }

    // returns the TV of the goal of the effect of the pair, returns null if it doesn't lead to a goal
    public function retDecisionMakingCandidateTv(pair:Pair):Tv {
        throw "VIRTUAL METHOD CALLED";
    }

    // returns the candidates for decision making which have parEvents as a precondition together with exp()
    public function retDecisionMakingCandidatesForCurrentEvents(parEvents: Array<Term>): Array<{pair:Pair, exp:Float}> {
        throw "VIRTUAL METHOD CALLED";
    }

    // checks if it is eternal goal
    public function isEternalGoal(t:Term): Bool {
        return eternalGoals.filter(v -> TermUtils.equal(t, v)).length > 0;
    }
}

/* commented because it is outdated
// goal system, manages priority and treatment of (sub)-goals
class GoalSystem extends AbstractGoalSystem {
    // active goals
    public var activeGoals:Array<ActiveGoal> = [];
    
    public function new() {
        super();
    }

    public override function tryAddDerivedGoal(term:Term, tv:Tv, stamp:Stamp, time:Int) {
        var activeGoalsWithSameTerm:Array<ActiveGoal> = activeGoals.filter(iGoal -> TermUtils.equal(iGoal.term, term));

        var wasOverlapDetected = false; // was any stamp overlap detected?

        if (activeGoalsWithSameTerm.length > 0) {
            // revise existing goals if possible
            for(iActiveGoal in activeGoalsWithSameTerm) {
                if (Stamp.checkOverlap(iActiveGoal.stamp, stamp, false)) {
                    wasOverlapDetected = true;
                }
                else { // must not overlap
                    iActiveGoal.tv = Tv.revision(iActiveGoal.tv, tv);
                    iActiveGoal.stamp = Stamp.merge(iActiveGoal.stamp, stamp);
                }
            }
        }

        var exists = activeGoalsWithSameTerm.length > 0;
        if (!exists && !wasOverlapDetected) { // only add it if no overlap was detected
            activeGoals.push(new ActiveGoal(term, tv, stamp, time));
        }
    }

    public override function step(executive:Executive) {
        // flush goals and reinstantiate eternal goals
        if (executive.cycle % 40 == 0) {
            activeGoals = [];                        // flush goals
            
            // instantiate eternal goals
            for(iEternalGoal in eternalGoals) {
                tryAddDerivedGoal(TermUtils.cloneShallow(iEternalGoal), new Tv(1.0, 0.9999), executive.createStamp(), executive.cycle);
            }
        }
    }

    public override function goalDerivation(executive:Executive) {
        var sampledGoal = sample(rng, cycle);
        if (sampledGoal != null) {
            // try to derive goals
            var matchingPairs = executive.pairs.filter(iPair -> Par.checkSubset(iPair.effect, new Par([sampledGoal.term])));
            matchingPairs =
                //executive.pairs // commented because it is a bug
                matchingPairs
                .filter(iPair -> iPair.cond.events.length == 1); // HACK< only accept single par conj for now >
            for(iMatchingPair in matchingPairs) {
                var goalTerm:Term = iMatchingPair.cond.events[0]; // TODO TODO TODO< rewrite Par to parallel conjunction >

                var compoundTv:Tv = new Tv(iMatchingPair.calcFreq(), iMatchingPair.calcConf());
                var goalTv = Tv.deduction(compoundTv, sampledGoal.tv);

                // (&/, a, ^b) =/> c    c!  |- (&/, a, ^b)! |- a!
                if(false) trace('derived goal ${iMatchingPair.convToStr()} |- ${TermUtils.convToStr(goalTerm)}! {${goalTv.freq} ${goalTv.conf}}');

                var conclStamp:Stamp = Stamp.merge(iMatchingPair.stamp, sampledGoal.stamp); // we need to merge stamp because it is a conclusion
                goalSystem.tryAddDerivedGoal(goalTerm, goalTv, conclStamp, cycle);
            }
        }
    }

    public function sample(rng:Rule30Rng, time:Int): ActiveGoal {
        if (activeGoals.length == 0) {
            return null; // didn't find any goal
        }

        var idx = rng.nextInt(activeGoals.length);
        return activeGoals[idx];
    }

    public override function retNoneternalGoals(): Array<ActiveGoal> {
        return activeGoals;
    }
}





// goal system, manages priority and treatment of (sub)-goals
// uses decaying goals
class DecayingGoalSystem extends AbstractGoalSystem {
    // active goals
    public var activeGoals:Array<ActiveGoal> = [];
    
    public var activeGoalsMaxSize:Int = 100;

    public function new() {
        super();
    }

    public override function tryAddDerivedGoal(term:Term, tv:Tv, stamp:Stamp, time:Int) {
        var activeGoalsWithSameTerm:Array<ActiveGoal> = activeGoals.filter(iGoal -> TermUtils.equal(iGoal.term, term));

        var wasOverlapDetected = false; // was any stamp overlap detected?

        if (activeGoalsWithSameTerm.length > 0) {
            // revise existing goals if possible
            for(iActiveGoal in activeGoalsWithSameTerm) {
                if (TermUtils.equal(iActiveGoal.term, term)) {
                    if (Stamp.checkOverlap(iActiveGoal.stamp, stamp, false)) {
                        wasOverlapDetected = true;
                    }
                    else { // must not overlap
                        iActiveGoal.tv = Tv.revision(iActiveGoal.tv, tv);
                        iActiveGoal.stamp = Stamp.merge(iActiveGoal.stamp, stamp);
                    }
                }
            }
        }

        var exists = activeGoalsWithSameTerm.length > 0;
        if (!exists && !wasOverlapDetected) { // only add it if no overlap was detected
            activeGoals.push(new ActiveGoal(term, tv, stamp, time));
        }
    }

    // helper to compute the relative priority of a goal
    private function calcRelativePri(activeGoal:ActiveGoal, time:Int): Float {
        var timediff = time-activeGoal.creationTime;
        var decay = Math.exp(-decayrate*timediff);
        return decay*Tv.calcExp(activeGoal.tv.freq, activeGoal.tv.conf);
    }

    public override function step(executive:Executive) {
        // reinstantiate eternal goals
        if (executive.cycle % 40 == 0) {
            // instantiate eternal goals
            for(iEternalGoal in eternalGoals) {
                tryAddDerivedGoal(TermUtils.cloneShallow(iEternalGoal), new Tv(1.0, 0.9999), executive.createStamp(), executive.cycle);
            }
        }

        // limit size
        if (executive.cycle % 40 == 0) {
            var activeGoalsWithRelativePriority = activeGoals.map(v -> {goal:v, relativePriority:calcRelativePri(v, executive.cycle)});

            activeGoalsWithRelativePriority.sort((a, b) -> {
                if (a.relativePriority < b.relativePriority) {
                    return 1;
                }
                else if(a.relativePriority > b.relativePriority) {
                    return -1;
                }
                return 0;
            });

            // force to remove decayed goals
            activeGoalsWithRelativePriority = activeGoalsWithRelativePriority.filter(v -> v.relativePriority > 0.01);

            activeGoalsWithRelativePriority = activeGoalsWithRelativePriority.slice(0, activeGoalsMaxSize);
            
            if (false) { // debug entries in priority list?
                for(idx in 0...activeGoalsWithRelativePriority.length) {
                    var iGoal = activeGoalsWithRelativePriority[idx];
                    trace('[$idx]: term = ${TermUtils.convToStr(iGoal.goal.term)} t = ${iGoal.goal.creationTime}  pri = ${iGoal.relativePriority} stamp = ${iGoal.goal.stamp.convToStr()}');
                }
            }


            activeGoals = activeGoalsWithRelativePriority.map(v -> v.goal);
        }
    }

    public override function goalDerivation(executive:Executive) {
        var sampledGoal = sample(rng, cycle);
        if (sampledGoal != null) {
            // try to derive goals
            var matchingPairs = executive.pairs.filter(iPair -> Par.checkSubset(iPair.effect, new Par([sampledGoal.term])));
            matchingPairs =
                //executive.pairs // commented because it is a bug
                matchingPairs
                .filter(iPair -> iPair.cond.events.length == 1); // HACK< only accept single par conj for now >
            for(iMatchingPair in matchingPairs) {
                var goalTerm:Term = iMatchingPair.cond.events[0]; // TODO TODO TODO< rewrite Par to parallel conjunction >

                var compoundTv:Tv = new Tv(iMatchingPair.calcFreq(), iMatchingPair.calcConf());
                var goalTv = Tv.deduction(compoundTv, sampledGoal.tv);

                // (&/, a, ^b) =/> c    c!  |- (&/, a, ^b)! |- a!
                if(false) trace('derived goal ${iMatchingPair.convToStr()} |- ${TermUtils.convToStr(goalTerm)}! {${goalTv.freq} ${goalTv.conf}}');

                var conclStamp:Stamp = Stamp.merge(iMatchingPair.stamp, sampledGoal.stamp); // we need to merge stamp because it is a conclusion
                goalSystem.tryAddDerivedGoal(goalTerm, goalTv, conclStamp, cycle);
            }
        }
    }

    public var decayrate:Float = 0.0003; // decay rate of the goals

    public function sample(rng:Rule30Rng, time:Int): ActiveGoal {
        if (activeGoals.length == 0) {
            return null; // didn't find any goal
        }

        var mass:Float = 0.0;
        for(iGoal in activeGoals) {
            mass += calcRelativePri(iGoal, time);
        }


        // probabilistic selection
        var selectedMass = rng.nextFloat()*mass;
        var accu = 0.0;

        for(iGoal in activeGoals) {
            accu += calcRelativePri(iGoal, time);
            if (accu >= selectedMass) {
                return iGoal;
            }
        }
        return activeGoals[activeGoals.length-1];
    
    }

    public override function retNoneternalGoals(): Array<ActiveGoal> {
        return activeGoals;
    }

    public override function retDecisionMakingCandidatesForCurrentEvents(parEvents: Array<Term>): Array<{pair:Pair, exp:Float}> {
        return []; // nothing to do in this implementation
    }
}
 */

// goal system which uses a tree planning mechanism in a backward way
class TreePlanningGoalSystem extends AbstractGoalSystem {
    public var decayrate:Float = 0.0003; // decay rate of the goals

    public var decayThreshold = 0.01; // threshold for a goal to get removed

    public var roots:Array<PlanningTreeNode> = [];

    // acceleration structure for tree lookup by parallel events
    //    is lazily completely replaced to keep implementation simple
    private var nodesByCond:ByCond<PlanningTreeNode> = new ByCond<PlanningTreeNode>();

    public function new() {
        super();
    }

    // derives goals
    public override function goalDerivation(executive:Executive) {
        if (executive.cycle % 15 != 0) {
            return;
        }


        { // add root goals if they are not present
            var rootNodesToAdd = [];

            for(iEternalGoal in eternalGoals) {
                var isInRoots = roots.filter(iRoot -> {
                    return TermUtils.equal(iRoot.goalTerm, iEternalGoal); // NOTE< we can check the goal term because it is always present in the root nodes >
                }).length > 0;
                if (!isInRoots) {
                    // add node to roots
                    var createdChildren = new PlanningTreeNode(executive.cycle);
                    createdChildren.goalTerm = iEternalGoal;
                    createdChildren.goalTv = new Tv(1.0, 0.99999);
                    rootNodesToAdd.push(createdChildren);
                }
            }

            for(i in rootNodesToAdd) {
                roots.push(i);
            }
        }



        // tries to add a node to the node
        function tryAdd(node:PlanningTreeNode) {

            // * select matching pair

            var pairCandidates:Array<Pair> = executive.mem.pairs.filter(iPair -> {
                // we restrict outself to pairs which have only one effect
                // else it doesn't work
                // INVESTIAGTION< investigate if this is not needed!!!!!!! >
                if (iPair.effect.events.length > 1) {
                    return false;
                }

                if (node.goalTerm != null) { // doesn't have pair
                    return iPair.effect.hasEvent(node.goalTerm);
                }
                else {
                    return Par.checkSubset(iPair.effect, node.sourcePair.cond);
                }
            }); // select all pairs which have the goal as a effect

            for (iMatchingPair in pairCandidates) {
                // exp() must be over decision threshold!
                // else we add items to the tree which can never be fullfilled!
                {
                    var exp:Float = Tv.calcExp(iMatchingPair.calcFreq(), iMatchingPair.calcConf());
                    if (exp < executive.decisionThreshold) {
                        continue; // don't consider to add it because it will never get picked
                    }
                }

                // * check if it is already present:
                var isAlreadyPresent = false;
                for (iChildren in node.children) {
                    if (iChildren.sourcePair == iMatchingPair) {
                        isAlreadyPresent = true;
                        break; // optimization
                    }

                    /* commented because slow path and not needed
                    if (
                        TermUtils.equal(iChildren.sourcePair.act[0], iMatchingPair.act[0]) && // TODO< check sequence of actions >
                        Par.checkSame(iChildren.sourcePair.cond, iMatchingPair.cond) &&
                        Par.checkSame(iChildren.sourcePair.effect, iMatchingPair.effect)
                    ) {
                        isAlreadyPresent = true;
                        break; // optimization
                        
                    }
                    */
                }

                if (isAlreadyPresent) {
                    continue; // we don't need to add if it it is already present
                }

                
                // * add node

                var createdChildren = new PlanningTreeNode(executive.cycle);
                createdChildren.parent = node; // link to parent
                createdChildren.creationT = executive.cycle;
                createdChildren.sourcePair = iMatchingPair;
                node.children.push(createdChildren);

                
                { // add acceleration structure
                    nodesByCond.add(createdChildren.sourcePair.cond.events, createdChildren);
                }
            }
        }



        {
            // populate tree with Russian Roulette Path Termination criterion
            // we need this criterion because else the probability mass to add nodes tends to much to nodes which are deep inside the tree (which leads to useless nodes)
            // see https://www.youtube.com/watch?v=vPwiqXjDgeo
            var terminationProbability = 0.6;

            var maxTreeDepth = 2;

            function tryAddOrTerminate(node:PlanningTreeNode, treeDepth:Int) {
                if (treeDepth >= maxTreeDepth) {
                    return;
                }
                
                // try to add entries to node
                tryAdd(node);
                
                if (executive.rng.nextFloat() < terminationProbability) {
                    return; // terminate
                }

                // do the same recursivly
                if (node.children.length == 0) {
                    return;
                }
                // pick random children
                var idx = executive.rng.nextInt(node.children.length);
                tryAddOrTerminate(node.children[idx], treeDepth+1);
            }

            for(iRoot in roots) {
                tryAddOrTerminate(iRoot, 0);
            }
        }

        return; // return because the other algorithm doesn't work quite right



        {
            // * pick a random element from the tree
            var elementsOfTree = [];

            for(iRoot in roots) { // collect all node of the tree
                function addNodeAndChildrenRec(node:PlanningTreeNode) {
                    elementsOfTree.push(node);
                    for(iChildren in node.children) {
                        addNodeAndChildrenRec(iChildren);
                    }
                }

                addNodeAndChildrenRec(iRoot);
            }

            if (elementsOfTree.length == 0) {
                return;
            }
            var selectedNode: PlanningTreeNode = null;
            { // pick random node
                var idx = executive.rng.nextInt(elementsOfTree.length);
                selectedNode = elementsOfTree[idx];
            }

            tryAdd(selectedNode);
        }
        
        /* old code


        var sampledGoal = goalSystem.sample(rng, cycle);
        if (sampledGoal != null) {
            // try to derive goals
            var matchingPairs = pairs.filter(iPair -> Par.checkSubset(iPair.effect, new Par([sampledGoal.term])));
            matchingPairs = pairs.filter(iPair -> iPair.cond.events.length == 1); // HACK< only accept single par conj for now >
            for(iMatchingPair in matchingPairs) {
                var goalTerm:Term = iMatchingPair.cond.events[0]; // TODO TODO TODO< rewrite Par to parallel conjunction >

                var compoundTv:Tv = new Tv(iMatchingPair.calcFreq(), iMatchingPair.calcConf());
                var goalTv = Tv.deduction(compoundTv, sampledGoal.tv);

                // (&/, a, ^b) =/> c    c!  |- (&/, a, ^b)! |- a!
                if(false) trace('derived goal ${iMatchingPair.convToStr()} |- ${TermUtils.convToStr(goalTerm)}! {${goalTv.freq} ${goalTv.conf}}');

                var conclStamp:Stamp = Stamp.merge(iMatchingPair.stamp, sampledGoal.stamp); // we need to merge stamp because it is a conclusion
                goalSystem.tryAddDerivedGoal(goalTerm, goalTv, conclStamp, cycle);
            }
        }
         */
    }
    
/* commented because api is not compatible
    public override function tryAddDerivedGoal(term:Term, tv:Tv, stamp:Stamp, time:Int, source:Pair) {
        // TODO
    }
*/

    /*
    // helper to compute the relative priority of a goal
    private function calcRelativePri(activeGoal:ActiveGoal, time:Int): Float {
        var timediff = time-activeGoal.creationTime;
        var decay = Math.exp(-decayrate*timediff);
        return decay*Tv.calcExp(activeGoal.tv.freq, activeGoal.tv.conf);
    }
    */

    private function calcDecay(treeNode:PlanningTreeNode, currentT:Int, parentTv:Tv) {
        var tv = treeNode.retTv(parentTv);
        return treeNode.calcDecay(currentT, decayrate)*Tv.calcExp(tv.freq, tv.conf);
    }

    private function debugTree(executive:Executive) {
        function debugTreeRec(node:PlanningTreeNode, depth:Int) {
            var space:String = '  ';
            for(i in 0...depth) {
                space += "   ";
            }

            var nodeInfoStr:String = null;
            if (node.sourcePair != null) {
                nodeInfoStr = node.sourcePair.convToStr();
            }
            else {
                nodeInfoStr = TermUtils.convToStr(node.goalTerm);
            }

            Sys.println('$space$nodeInfoStr');

            for(iChildren in node.children) {
                debugTreeRec(iChildren, depth+1);
            }
        }

        Sys.println('t=${executive.cycle}  goal tree:');
        for (iRoot in roots) {
            debugTreeRec(iRoot, 0);
        }
    }

    public override function step(executive:Executive) {
        if (executive.cycle % 2500 == 0) {
            { // count number of tree nodes
            
                var nTreeNodes = 0; // counter for tree nodes

                function rec(node:PlanningTreeNode) {
                    nTreeNodes++;

                    for(iChildren in node.children) { // do the same for all children
                        rec(iChildren);
                    }
                }

                for(iRoot in roots) {
                    rec(iRoot);
                }

                Sys.println('goal system  #treeNodes=$nTreeNodes');
            }
            
            
            debugTree(executive);
        }

        


        if (executive.cycle % 100 == 0) { // prune : remove goals where the (decayed) exp(tv) * decay is below the threshold

            // checks if a treenode was decayed
            function checkDecayed(treeNode:PlanningTreeNode, parentTv:Tv) {
                return calcDecay(treeNode, executive.cycle, parentTv) < decayThreshold;
            }

            function pruneRec(node:PlanningTreeNode, parentTv:Tv) {
                node.children = node.children.filter(n -> !checkDecayed(n, parentTv)); // keep node if not decayed

                // do the same recursivly for all children
                for(iChildren in node.children) {
                    pruneRec(iChildren, node.retTv(parentTv));
                }
            }

            for(iRoot in roots) {
                pruneRec(iRoot, new Tv(1.0, 0.999999));
            } 
        }
    }

    public override function sample(rng:Rule30Rng, time:Int): ActiveGoal {
        return null;// sampling is not supported
    }

    public override function retNoneternalGoals(executive:Executive): Array<ActiveGoal> {
        return eternalGoals.map(term -> 
            new ActiveGoal(term, new Tv(1.0, 0.9999), executive.createStamp(), executive.cycle)
        );
    }

    public override function retDecisionMakingCandidateTv(pair:Pair):Tv {
        // TODO< compute the TV of the pair and the candidate in the exp() calculation >

        // searches all of the tree for the best node with the highest exp() 
        // in all nodes which have the effect of the pair as a condition

        // enumerate tree node candidates
        var treeNodeCandidates:Array<PlanningTreeNode> = [];
        
        function rec(node:PlanningTreeNode) {
            var add = false;
            
            // TODO< check if there is a bug in the subset computation >
            if (node.goalTerm != null) { // does this node have only a goal term?
                add = Par.checkSubset(new Par([node.goalTerm]), pair.effect); // add it if it is equal
            }
            else {
                add = Par.checkSubset(node.sourcePair.cond, pair.effect);
            }
            
            if (add) {
                treeNodeCandidates.push(node);
            }

            for(iChildren in node.children) { // do the same for all children
                rec(iChildren);
            }
        }

        for(iRoot in roots) {
            rec(iRoot);
        }



        // * compute candidate with best exp()
        if (treeNodeCandidates.length == 0) { // was no candidate found?
            return null;
        }
        
        var bestCandidateTv:Tv = treeNodeCandidates[0].retTv(null);
        var bestCandidateExp = Tv.calcExp(bestCandidateTv.freq, bestCandidateTv.conf);
        var bestCandidate:PlanningTreeNode = treeNodeCandidates[0];

        for(iCandidate in treeNodeCandidates) {
            var tempTv:Tv = iCandidate.retTv(null);
            var exp = Tv.calcExp(tempTv.freq, tempTv.conf);
            if (exp > bestCandidateExp) {
                bestCandidateTv = tempTv;
                bestCandidateExp = exp;
                bestCandidate = iCandidate;
            }
        }

        return bestCandidateTv;
    }

    public override function retDecisionMakingCandidatesForCurrentEvents(parEvents: Array<Term>): Array<{pair:Pair, exp:Float}> {
        var resultArr = [];

        {
            var candidateNodes:Array<PlanningTreeNode> = nodesByCond.queryByCond(parEvents)
                .filter(v -> !v.sourcePair.isConcurrentImpl) // only allow =/>
                .filter(ipTreeNode -> { // consider only candidates which fullfill not satisfied goals
                    if(ipTreeNode.sourcePair != null && Par.checkIntersect( ipTreeNode.sourcePair.effect, new Par(parEvents))) {
                        return false; // don't consider as candidate because the effects are already happening
                    }
                    
                    if(ipTreeNode.parent != null && ipTreeNode.parent.sourcePair != null) {
                        if(Par.checkIntersect( ipTreeNode.parent.sourcePair.effect, new Par(parEvents))) {
                            return false; // don't consider as candidate because the effects are already happening
                        }
                    }
                    return true;
                });
            
            for(iCandidateNode in candidateNodes) {
                var tv = iCandidateNode.retTv(null);
                var exp:Float = Tv.calcExp(tv.freq, tv.conf);
                resultArr.push({pair:iCandidateNode.sourcePair, exp:exp});
            }
        }
        /* correct slow path, commented because it is to slow

        // checks if the precondition fits and add it to the result if so
        function checkAndAddRec(node:PlanningTreeNode) {
            if (node.sourcePair != null) {
                var arePreconditionsFullfilled = Par.checkSubset(new Par(parEvents), node.sourcePair.cond); // condition must be subset
                if(arePreconditionsFullfilled) {
                    var tv = node.retTv(null); // OPTIMIZATION< might get optimized by passing in parent >
                    var exp:Float = Tv.calcExp(tv.freq, tv.conf);
                    resultArr.push({pair:node.sourcePair, exp:exp});
                }
            }
            
            for(iChildren in node.children) {
                checkAndAddRec(iChildren);
            }
        }

        for(iRoot in roots) {
            checkAndAddRec(iRoot);
        }
        */

        return resultArr;
    }
}

class PlanningTreeNode {
    public var parent:PlanningTreeNode = null; // null means that it doesn't have a parent
    public var children:Array<PlanningTreeNode> = [];

    public var creationT:Int; // time of creation of this node, used for decay

    public var goalTerm:Term; // actual goal term
    public var goalTv:Tv = null; // tv of the goal, must be null if sourcePair is not null!
    public var sourcePair:Pair = null; // can be null if it is a root goal

    public function new(creationT) {
        this.creationT = creationT;
    }

    public function calcDecay(currentT:Int, decayRate:Float) {
        var diff = currentT - creationT;
        return Math.exp(-diff * decayRate);
    }

    // /param parentTv is the TV of the parent, special case is if it is null, it will be computed by demand if it is null
    public  function retTv(parentTv:Tv):Tv {
        if (parentTv == null) { // do we need to compute parent-TV?
            if (sourcePair != null) {
                parentTv = parent.retTv(null);
            }
            else {
                parentTv = goalTv;
            }
        }

        if (sourcePair != null) {
            var tv = new Tv(sourcePair.calcFreq(), sourcePair.calcConf());
            return Tv.deduction(tv, parentTv); // we must compute deduction, because the derived goal is computed with deduction
        }
        return goalTv;
    }
}


// forward chainer which acts as a planner
class ForwardChainer {
    public function new() {}

    // dedicates one processing step
    public static function step(currentEvents:Array<Term>, chainDepth:Int, exec:Executive): Array<{pair:Pair, exp:Float}> {
        // sample the current events and try to chain to a goal

        if (currentEvents.length == 0) {
            return []; // nothing to sample
        }


        var idx:Int = exec.rng.nextInt(currentEvents.length);
        var selChainEvent: Term = currentEvents[idx]; // select event to try to chain
        var chainTv: Tv = new Tv(1.0, 0.99999); // tv of chaining - assumed to be axiomatic

        var chain: Array<Term> = [selChainEvent]; // chain of events
        var combinedStamp: Stamp = exec.createStamp(); // TODO< get stamp from selected event ! >

        var chain2 = [];

        for(iChainDepth in 0...chainDepth) {
            var firstChainElementCandidate:Array<Pair> = exec.mem.pairs.filter(iPair -> iPair.cond.hasEvent(selChainEvent));
            
            // sample first chain element candidate
            if (firstChainElementCandidate.length == 0) {
                return []; // nothing to sample
            }



            var selChainPair0Idx:Int = exec.rng.nextInt(firstChainElementCandidate.length);
            var selChainPair0: Pair = firstChainElementCandidate[selChainPair0Idx];

            chain2.push(selChainPair0);

            if (Stamp.checkOverlap(selChainPair0.stamp, combinedStamp)) {
                return []; // we don't allow stamp overlap!
            }
            combinedStamp = Stamp.merge(combinedStamp, selChainPair0.stamp);

            selChainEvent = selChainPair0.effect.events[0]; // TODO< select any event >
            chainTv = Tv.induction(chainTv, new Tv(selChainPair0.calcFreq(), selChainPair0.calcConf()));

            for(iAct in selChainPair0.act) {
                chain.push(iAct);
            }
            chain.push(selChainEvent);
        }


        { // check if we hit a goal with the effect of the chained sequence
            var hitGoal = false; // did we hit a goal with the derived seq?
            for(iGoal in exec.goalSystem.retNoneternalGoals(exec)) {
                if (TermUtils.equal(iGoal.term, selChainEvent)) {
                    hitGoal = true;
                    break; // optimization
                }
            }

            // TODO< compute exp correctly >
            hitGoal = hitGoal || exec.goalSystem.retDecisionMakingCandidatesForCurrentEvents([selChainEvent]).length > 0; // did we hit a derived goal?

            if (!hitGoal) {
                return[]; // because we derived something which doesn't hit a goal, it's pointless!
            }
        }

        // we are only here if we hit a goal with the chained effect

        // execute first element
        return [
            {pair: chain2[0], exp:chainTv.exp()} // return only first chain element because our plan starts with it
        ];


        /* commented because old code which stores it, we can't do this and must use it for planning
        // * store derivation(s)

        { // build derived pair
            Assert.enforce(chain.length == 5, "expect specific length!"); // we assume that the chain is (&/, a, ^b, c, ^d, e)

            // build  (&/, a, ^b, ^d) =/> e
            var conclPair:Pair = new Pair(combinedStamp);
            conclPair.cond = new Par([chain[0]]);
            conclPair.act = [chain[1], chain[3]]; // TODO< implement for any length of ops seqs >
            conclPair.effect = new Par([chain[4]]);

            exec.mem.addPair(conclPair); // TODO< check if conclusion exist already >
        }

        // TODO< build and add (&/, a, ^b, c, ^d, e)
        */
    }
}


class ActiveGoal {
    public var term:Term;
    public var tv:Tv;
    public var stamp:Stamp;
    public var creationTime:Int; // creation time in cycles

    public function new(term, tv, stamp, creationTime) {
        this.term = term;
        this.tv = tv;
        this.stamp = stamp;
        this.creationTime = creationTime;
    }
}

// anticipated event which is anticipated because a action was done which leads to some anticipated effect
class InflightAnticipation {
    public var origin:Pair; // origin of the anticipation: ex: (&/, a, ^b) =/> c
    public var deadline:Int; // deadline: max global cycle time until the anticipated event must have been occured

    public function new(origin, deadline) {
        this.origin = origin;
        this.deadline = deadline;
    }
}

class Par {
    public var events:Array<Term> = []; // parallel events

    public function new(events) {
        this.events = events;
    }

    public function hasEvent(e:Term) {
        return events.filter(ie -> TermUtils.equal(ie, e)).length > 0;
    }

    // extremely simple check if it is the same, doesn't check out of order!!!
    public static function checkSame(a:Par, b:Par) {
        if (a.events.length != b.events.length) {
            return false;
        }

        for(idx in 0...a.events.length) {
            if (!TermUtils.equal(a.events[idx], b.events[idx])) {
                return false;
            }
        }
        return true;
    }

    public static function checkIntersect(a:Par, b:Par): Bool {
        return checkSubset(a, b) || checkSubset(b, a);
    }

    // checks if b is a subset of a
    public static function checkSubset(a:Par, b:Par) {
        // all events in b must appear in a
        return b.events.filter(ib -> a.hasEvent(ib)).length == b.events.length;
    }
}

class Pair {
    public var cond:Par = null;
    public var act:Array<Term> = []; // TODO< rename to ops >
    public var effect:Par = null;

    public var evidencePositive = 1; // positive evidence counter
    public var evidenceCnt = 1; // evidence counter

    public var stamp:Stamp;

    public var isConcurrentImpl = false; // is it =|> instead of =/> ?

    public function new(stamp) {
        this.stamp = stamp;
    }

    public function calcConf() {
        // see http://alumni.media.mit.edu/~kris/ftp/Helgason%20et%20al-AGI2013.pdf
        return evidenceCnt / (evidenceCnt + 1.0);
    }

    public function calcFreq() {
        var p:Float = evidencePositive;
        return p / evidenceCnt;
    }

    public function convToStr():String {
        if (isConcurrentImpl) {
            return '${cond.events.map(v -> TermUtils.convToStr(v))} =|> ${effect.events.map(v -> TermUtils.convToStr(v))} {${calcFreq()} ${calcConf()}} // cnt=$evidenceCnt';
        }

        return '(&/,${cond.events.map(v -> TermUtils.convToStr(v))},${act.map(v -> TermUtils.convToStr(v))}) =/> ${effect.events.map(v -> TermUtils.convToStr(v))} {${calcFreq()} ${calcConf()}} // cnt=$evidenceCnt';
    }
}

// registered action
class Act {
    public var name:String;

    // action is not possible as long as the action gets triggered below the peroid limit
    public var refractoryPeriod:Int = 0;
    public var refractoryPeriodCooldown:Int = 0;

    public function new(name:String) {
        if (name.charAt(0) != '^') {
            throw 'name $name must start with ^ !';
        }

        this.name = name;
    }

    /*abstract*/public function exec() {
        throw "NOT IMPLEMENTED!";
    }
}


// op for testing if op was called
// used for self-tests, unittests, etc.
class CountOp extends Act {
    public var counter:Int = 0;

    public function new(name:String) {
        super(name);
    }

    public override function exec() {
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

    public override function exec() {
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

    public override function exec() {
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

    public override function exec() {
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

    public override function exec() {
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

    public override function exec() {
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

                stateAsStr += ' S$enc$idx';
                res.push(Term.Name('S$enc$idx'));
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
            spawnedProj.velX = 0.02 * (1); // TODO< get from look direction >
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
                        Sys.println('seaquest  enemy hit!');

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



class Assert {
    // contract programming
    public static function enforce(b:Bool, msg:String) {
        if (!b) {
            throw msg;
        }
    }
}

// incremental gaussian distribution estimator
// see http://datagenetics.com/blog/november22017/index.html
class IncrementalCentralDistribution {
    public function new() {}

    public function next(x:Float) {
        var nextMean:Float = mean + (x - mean)/(n+1);
        var nextS:Float = s + (x - mean)*(x - nextMean);

        mean = nextMean;
        s = nextS;
        n++;
    }

    public function calcVariance():Float {
        return Math.sqrt(s/n);
    }

    public var n:Int = 0; // TODO< should be Long integer >
    public var mean:Float = 0.0;
    public var s:Float = 0.0;
}

// random generator which uses rule30
class Rule30Rng {
    static function main() {
        var rng = new Rule30Rng();
        
        for(i in 0...30) {
        	trace('${rng.nextFloat()}');
        }
    }
    
    
    static function calcRule30(a:Bool,b:Bool,c:Bool) {
        //100 	011 	010 	001
        return
            (a && !b && !c) ||
            (!a && b && c) ||
            (!a && b && !c) ||
            (!a && !b && c);
    }
    
    public function new() {}
    
    function nextIntInternal():Int {
        var vInt = 0;
        calcNextVec();
        
        for(idx in 0...bVec.length) {
            if(bVec[idx]) {
            	vInt += (1 << idx);
        	}
        }

        return vInt;
    }

    public function nextFloat():Float {
        return nextIntInternal() / (1 << bVec.length);
    }

    public function nextInt(max:Int): Int {
        return nextIntInternal() % max;
    }
    
    // computes next vector with rule30
    function calcNextVec() {
        bVec = [for (idx in 0...bVec.length) calcRule30(bVec[(idx+bVec.length-1) % bVec.length], bVec[idx], bVec[(idx+bVec.length+1) % bVec.length])];
    }
    
	// we can only compute for 30 bits on javascript targets
    var bVec = [for (idx in 0...30) Std.random(2) == 1];
}



// TODO LATER< terms can act like neurons and send spikes to other terms, some spikes can add up with ded for seq spikes >
