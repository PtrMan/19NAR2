// TODO< decay goals by delta-time >
// TODO< probabilistically select goals by exp() * decay >

// TODO< add eternal goals to goal system >
// TODO< copy goal of eternal goal in goal system every n cycles >

// TODO< do experiment fixure for pong1 too >
// TODO< add handling of empty cycles (skip trace items) >
// TODO< add pong2 with automatic moving bat >
// TODO< add stochastic environment >

// TODO< pong4 - pong with stochastic timing >



// decision making experiment

// features:
// * anticipation
// * decision making: actions can have a refractory peroid to avoid spamming the environment with pointless actions

// * flush goals after a fixed interval - like 50 steps, down to basic goal


class ExpDescn2 {

    
    // tests if the executive can confirm a anticipation correctly
    public static function testAnticipationConfirm1() {
        var uut:Executive = new Executive();
        uut.randomActProb = 0.0; // we must disable random actions

        { // add anticipation which is assumed to be inflight
            var pair = new Pair();
            pair.effect = new Par([new Term("a")]);

            uut.anticipationsInflight.push(new InflightAnticipation(pair, 5));
        }
        
        uut.step([new Term("a"), new Term("b")]);

        Assert.enforce(uut.anticipationsInflight.length == 0, "anticipation must have been confirmed!");
    }
    
    // tests if the executive can confirm a anticipation correctly
    public static function testAnticipationConfirm2() {
        var uut:Executive = new Executive();
        uut.randomActProb = 0.0; // we must disable random actions

        { // add anticipation which is assumed to be inflight
            var pair = new Pair();
            pair.effect = new Par([new Term("a"), new Term("b")]);

            uut.anticipationsInflight.push(new InflightAnticipation(pair, 5));
        }
        
        uut.step([new Term("a")]);

        Assert.enforce(uut.anticipationsInflight.length == 1, "anticipation must not have been confirmed!");
    }

    public static function main() {
        // short selftests
        testAnticipationConfirm1();
        testAnticipationConfirm2();

        var nExperimentThreads = 6; // number of threads for experiments


        var dbgCyclesVerbose = false; // debugging : are cycles verbose?

        var alien1RatioDist:IncrementalCentralDistribution = new IncrementalCentralDistribution();

        // does run one experiment with the reasoner
        function doExperimentWithExecutive(executive:Executive, cycles:Int) {
            executive.randomActProb = 0.12;
            
            /*
            var pong1:Pong1 = new Pong1(executive);

            // implant evidence to see if decision making is working
            {
                var createdPair = new Pair();
                createdPair.cond = new Par([new Term("l")]);
                createdPair.act = "^r";
                createdPair.effect = new Par([new Term("c")]);
                executive.pairs.push(createdPair);
            }
            //*/

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
            for(iEvidence in executive.pairs) {
                Sys.println(iEvidence.convToStr());
            }

            // add hit ratio to distribution
            alien1RatioDist.next(alien1.cntAliensHit / alien1.cntShoots);

            // print statistics of world:
            alien1.printStats();
        }

        //trace(Par.checkSubset(new Par([new Term("a")]), new Par([new Term("a")])));

        var numberOfExperiments = 20;

        var nActiveExperimentThreads = 0; // how many threads are active for the experiment?
        var nActiveExperimentThreadsLock:sys.thread.Mutex = new sys.thread.Mutex();

        var numberOfDoneExperiments = 0; // how many experiments were done until now?

        // do experiments with executive/reasoner
        while(numberOfDoneExperiments < numberOfExperiments) {
            // wait as long as there are no available workthreads
            while(true) {
                nActiveExperimentThreadsLock.acquire();
                var activeThreads:Int = nActiveExperimentThreads;
                nActiveExperimentThreadsLock.release();
                
                if (activeThreads < nExperimentThreads) {
                    break;
                }
                
                Sys.sleep(0.08);
            }
            Sys.println('start thread');

            #if (target.threaded)
            sys.thread.Thread.create(() -> {
                nActiveExperimentThreadsLock.acquire();
                nActiveExperimentThreads++;
                nActiveExperimentThreadsLock.release();
                var cycles:Int = 35000;
                var executive:Executive = new Executive();
                doExperimentWithExecutive(executive, cycles);
                
                numberOfDoneExperiments++; // bump counter

                nActiveExperimentThreadsLock.acquire();
                nActiveExperimentThreads--;
                nActiveExperimentThreadsLock.release();
            });
            #end

            Sys.println('alien1 hit ratio mean=${alien1RatioDist.mean} variance=${alien1RatioDist.calcVariance()} n=${alien1RatioDist.n}');
        }

    }
}

class Executive {
    public var acts:Array<Act> = []; // list of all actions
    
    public function new() {
        // the trace just needs 3 elements for now
        trace.push(new Par([]));
        trace.push(new Par([]));
        trace.push(new Par([]));
    }

    var queuedAct: String = null;
    var queuedActOrigin: Pair = null; // origin of the queued action if it was done by the executive

    var trace:Array<Par> = [];

    public var randomActProb:Float = 0.0; // config - propability to do random action

    public var decisionThreshold:Float = 0.4; // config

    public var anticipationDeadline = 20; // config - anticipation deadline in cycles


    public var cycle:Int = 0; // global cycle timer

    public var dbgEvidence = false; // debugging - debug new and revised evidence?

    public var rng:Rule30Rng = new Rule30Rng();

    public function goalNow(g:Term) {
        // check and exec if it is a action
        var isAction = g.content.charAt(0) == '^';
        if (isAction) {
            execAct(g.content, null);
        }

        // record to trace
        this.trace[0].events.push(g);
    }

    public function step(parEvents:Array<Term>) {
        // * try to confirm anticipations
        anticipationTryConfirm(parEvents);

        // * advance time by one step
        this.trace[2] = this.trace[1];
        this.trace[1] = this.trace[0];
        this.trace[0] = new Par([]);
        this.trace[0].events = parEvents;        

        { // do random action
            if(rng.nextFloat() < randomActProb && queuedAct == null) { // do random action
                var possibleActs = acts.filter(iAct -> iAct.refractoryPeriodCooldown <= 0); // only actions which are cooled down are possible as candidates

                var idx=Std.random(possibleActs.length);
                queuedAct = possibleActs[idx].name; // queue action as next action
                queuedActOrigin = null; // has no origin because it was done by random
            }
        }
        
        if (queuedAct != null) {
            execAct(queuedAct, queuedActOrigin);

            // record to trace
            this.trace[0].events.push(new Term(queuedAct));
        }
        
        var candidates:Array<Pair> = [];// candidates for decision making in this step
        { // * compute candidates for decision making in this step
            candidates = pairs.filter(v -> Par.checkSubset(new Par(parEvents), v.cond));
        }

        // * decision making
        queuedAct = null;
        queuedActOrigin = null;
        var bestDecisionMakingCandidate:Pair = selBestAct(filterCandidatesByGoal(candidates));
        if (bestDecisionMakingCandidate != null) {
            var bestDecisionExp:Float = calcExp(bestDecisionMakingCandidate.calcFreq(), bestDecisionMakingCandidate.calcConf());
            
            if (dbgDescisionMakingVerbose) trace('decsn making $bestDecisionExp > $decisionThreshold');
            
            if (
                bestDecisionExp > decisionThreshold && 
                retActByName(bestDecisionMakingCandidate.act).refractoryPeriodCooldown <= 0 // is it possible to execute the action based on refractory period?
            ) {
                queuedAct = bestDecisionMakingCandidate.act; // queue action for next timestep
                queuedActOrigin = bestDecisionMakingCandidate;
            }
        }



        // * store sequences if possible
        {
            // do terms contain a action?
            function containsAction(terms:Array<Term>): Bool {
                return terms.filter(v -> v.content.charAt(0) == '^').length > 0;
            }

            // aren't terms only actions?
            function containsAnyNonaction(terms:Array<Term>): Bool {
                return terms.filter(v -> v.content.charAt(0) != '^').length > 0;
            }

            if (
                !containsAction(this.trace[2].events) && // necessary because else it builds wrong conclusion (&/, [a], ^x) =/> y from [a, ^y] [^x] [y]
                containsAnyNonaction(this.trace[2].events) && containsAction(this.trace[1].events) && containsAnyNonaction(this.trace[0].events)) { // has at least one (&/, events, ^action) =/> effect term
                var nonactionsOf2:Array<Term> = this.trace[2].events.filter(v -> v.content.charAt(0) != '^');
                var actionsOf1:Array<Term> = this.trace[1].events.filter(v -> v.content.charAt(0) == '^');
                var nonactionsOf0:Array<Term> = this.trace[0].events.filter(v -> v.content.charAt(0) != '^');
                
                {

                    for(iActionTerm in actionsOf1) { // iterate over all actions done at that time
                        if(dbgEvidence) trace('evidence ${nonactionsOf2.map(v -> v.content)} ${actionsOf1.map(v -> v.content)} =/> ${nonactionsOf0.map(v -> v.content)}');
                        
                        // adds new evidence
                        function addEvidence(conds:Array<Term>, effects:Array<Term>) {
                            if (Par.checkIntersect(new Par(conds), new Par(effects))) {
                                return; // exclude (&/, a, ^b) =/> a
                            }

                            for(iPair in pairs) { // search for existing evidence and try to revise
                                ////trace('cs ${Par.checkSubset(iPair.cond, new Par(conds))} ${iPair.cond.events.map(v ->v.content)} ${new Par(conds).events.map(v->v.content)}');
                                
                                if (
                                    iPair.act == iActionTerm.content &&
                                    Par.checkSubset(iPair.cond, new Par(conds))
                                ) {
                                    // iPair.evidenceCnt++; // commented here because neg evidence should only come from neg-confirm, because we assume a open-world

                                    if (Par.checkSubset(iPair.effect, new Par(effects))) {
                                        iPair.evidenceCnt++;
                                        iPair.evidencePositive++;
                                    }
                                }
                            }

                            var existsEvidence = false; // does exact evidence exist?
                            for(iPair in pairs) { // search for exact evidence
                                if (
                                    iPair.act == iActionTerm.content &&
                                    Par.checkSame(iPair.cond, new Par(conds))
                                ) {
                                    if (Par.checkSame(iPair.effect, new Par(effects))) {
                                        existsEvidence = true;
                                    }
                                }
                            }

                            if (!existsEvidence) { // create new evidence if it doesn't yet exist
                                
                                // store pair
                                var createdPair:Pair = new Pair();
                                createdPair.cond = new Par(conds);
                                createdPair.act = iActionTerm.content;
                                createdPair.effect = new Par(effects);

                                if(dbgEvidence) trace('create new evidence ${createdPair.convToStr()}');

                                pairs.push(createdPair);
                            }
                        }

                        addEvidence(nonactionsOf2, nonactionsOf0);
                        
                        // add evidence of combinations of single events of cond and effect
                        if (nonactionsOf2.length > 1) {
                            for(iCond in nonactionsOf2) {
                                addEvidence([iCond], nonactionsOf0);
                            }
                        }

                        if (nonactionsOf0.length > 1) {
                            for(iEffect in nonactionsOf0) {
                                addEvidence(nonactionsOf2, [iEffect]);
                            }
                        }
                        
                        if (nonactionsOf2.length > 1 && nonactionsOf0.length > 1) {
                            for(iCond in nonactionsOf2) {
                                for (iEffect in nonactionsOf0) {
                                    addEvidence([iCond], [iEffect]);
                                }
                            }
                        }
                    }
                }
            }
        }

        anticipationMaintainNegAnticipations();
        decisionmakingActionCooldown();
        goalSystem.step(cycle); // let the goal system manage eternal goals etc
        goalDerivation();

        cycle++; // advance global cycle timer
    }

    // derives goals
    private function goalDerivation() {
        var sampledGoal = goalSystem.sample(rng);
        if (sampledGoal != null) {
            // try to derive goals
            var matchingPairs = pairs.filter(iPair -> Par.checkSubset(iPair.effect, new Par([sampledGoal.term])));
            matchingPairs = pairs.filter(iPair -> iPair.cond.events.length == 1); // HACK< only accept single par conj for now >
            for(iMatchingPair in matchingPairs) {
                var goalTerm:Term = iMatchingPair.cond.events[0]; // TODO TODO TODO< rewrite Par to parallel conjunction >

                var compoundTv:Tv = new Tv(iMatchingPair.calcFreq(), iMatchingPair.calcConf());
                var goalTv = Tv.deduction(compoundTv, sampledGoal.tv);

                // (&/, a, ^b) =/> c    c!  |- (&/, a, ^b)! |- a!
                if(false) trace('derived goal ${iMatchingPair.convToStr()} |- ${goalTerm.content}! {${goalTv.freq} ${goalTv.conf}}');

                goalSystem.tryAddDerivedGoal(goalTerm, goalTv);
            }
        }
    }

    // decrements the remaining refractory period
    private function decisionmakingActionCooldown() {
        for (iAct in acts) {
            iAct.refractoryPeriodCooldown--;
        }
    }

    public var dbgAnticipationVerbose = false; // are anticipations verbose?

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
    function filterCandidatesByGoal(candidates:Array<Pair>):Array<Pair> {
        var res = [];
        for(iCandi in candidates) {
            var add=false;

            var sampledGoals = [];
            { // sample some goals
                var thisSampledGoal = goalSystem.sample(rng);
                if (thisSampledGoal != null) {
                    sampledGoals.push(thisSampledGoal);
                }
            }

            for(iGoal in sampledGoals) {
                for(iEffect in iCandi.effect.events) {
                    if (Term.cmp(iEffect, iGoal.term)) {
                        add = true;
                        break; // optimization
                    }
                }
            }

            if (add) {
                res.push(iCandi);
            }
        }

        return res;
    }

    function retActByName(actName:String): Act {
        return acts.filter(iAct -> iAct.name == actName)[0];
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

    public var dbgDescisionMakingVerbose = false; // debugging : is decision making verbose
    public var dbgExecVerbose = false; // debugging : is execution of ops verbose?

    // select best action
    public function selBestAct(candidates:Array<Pair>): Pair {
        if (dbgDescisionMakingVerbose) trace('selBestAct() ${candidates.length}');
        
        if (candidates.length == 0) {
            return null; // no action
        }

        var bestExp:Float = calcExp(candidates[0].calcFreq(), candidates[0].calcConf());
        var bestCandidate = candidates[0];

        for(iCandidate in candidates) {
            var thisExp:Float = calcExp(iCandidate.calcFreq(), iCandidate.calcConf());
            if (thisExp > bestExp) {
                bestExp = thisExp;
                bestCandidate = iCandidate;
            }
        }

        if (dbgDescisionMakingVerbose) trace('FOUND best act candidate ${bestCandidate.convToStr()}');

        return bestCandidate;
    }

    // TODO< move to TV >
    private static function calcExp(freq:Float, conf:Float) {
        return (freq - 0.5) * conf + 0.5;
    }

    public var pairs:Array<Pair> = []; // all known pairs

    public var anticipationsInflight:Array<InflightAnticipation> = []; // anticipations in flight

    public var goalSystem:GoalSystem = new GoalSystem();
}


class AbstractGoalSystem {
    public var eternalGoals:Array<Term> = []; // list of all eternal goals which have to get pursued by the system
}

// goal system, manages priority and treatment of (sub)-goals
class GoalSystem extends AbstractGoalSystem {
    // active goals
    public var activeGoals:Array<ActiveGoal> = [];
    
    public function new() {}

    // try to add a derived goal if it doesn't exist already
    // TODO< add stamps as arguments >
    public function tryAddDerivedGoal(term:Term, tv:Tv) {
        var activeGoalsWithSameTerm:Array<ActiveGoal> = activeGoals.filter(iGoal -> iGoal.term.content == term.content);

        if (activeGoalsWithSameTerm.length > 0) {
            // TODO< check stamp before revising, don't add goal if all stamps overlap ! >

            // revise existing
            for(iActiveGoal in activeGoalsWithSameTerm) {
                iActiveGoal.tv = Tv.revision(iActiveGoal.tv, tv);
            }
        }

        var exists = activeGoalsWithSameTerm.length > 0;
        if (!exists) {
            activeGoals.push(new ActiveGoal(term, tv));
        }
    }

    // /param cycle is the global cycle time of the executive
    public function step(cycle:Int) {
        // flush goals and reinstantiate eternal goals
        if (cycle % 40 == 0) {
            activeGoals = [];                        // flush goals
            
            // instantiate eternal goals
            for(iEternalGoal in eternalGoals) {
                tryAddDerivedGoal(iEternalGoal.clone(), new Tv(1.0, 0.9999));
            }
        }
    }

    // sample a goal based on probability distribution
    public function sample(rng:Rule30Rng): ActiveGoal {
        if (activeGoals.length == 0) {
            return null; // didn't find any goal
        }

        var idx = rng.nextInt(activeGoals.length);
        return activeGoals[idx];
    }
}

class ActiveGoal {
    public var term:Term;
    public var tv:Tv;

    public function new(term, tv) {
        this.term = term;
        this.tv = tv;
    }
}

class Tv {
    public var freq:Float = 0.0;
    public var conf:Float = 0.0;

    public function new(freq, conf) {
        this.freq = freq;
        this.conf = conf;
    }

    public static function deduction(a, b) {
        var f = and(a.freq, b.freq);
        var c = and3(a.conf, b.conf, f);
        return new Tv(f, c);
    }

    public static function revision(a: Tv, b: Tv): Tv {
        var w1 = c2w(a.conf);
        var w2 = c2w(b.conf);
        var w = w1 + w2;
        return new Tv((w1 * a.freq + w2 * b.freq) / w, w2c(w));
    }

    static function w2c(w) { 
        var horizon = 1.0;
        return w / (w + horizon);
    }

    static function c2w(c: Float): Float {
        var horizon = 1.0;
        return horizon * c / (1.0 - c);
    }

    static function and(a:Float, b:Float) {
        return a*b;
    }
    static function and3(a:Float, b:Float, c:Float) {
        return a*b*c;
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
        return events.filter(ie -> Term.cmp(ie, e)).length > 0;
    }

    // extremely simple check if it is the same, doesn't check out of order!!!
    public static function checkSame(a:Par, b:Par) {
        if (a.events.length != b.events.length) {
            return false;
        }

        for(idx in 0...a.events.length) {
            if (!Term.cmp(a.events[idx], b.events[idx])) {
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
    public var act:String = "";
    public var effect:Par = null;

    public var evidencePositive = 1; // positive evidence counter
    public var evidenceCnt = 1; // evidence counter

    public function new() {}

    public function calcConf() {
        // see http://alumni.media.mit.edu/~kris/ftp/Helgason%20et%20al-AGI2013.pdf
        return evidenceCnt / (evidenceCnt + 1.0);
    }

    public function calcFreq() {
        var p:Float = evidencePositive;
        return p / evidenceCnt;
    }

    public function convToStr():String {
        return '(&/,${cond.events.map(v -> v.content)},$act) =/> ${effect.events.map(v -> v.content)} {${calcFreq()} ${calcConf()}} // cnt=$evidenceCnt';
    }
}

class Term {
    public var content:String = "";

    public function new(content) {
        this.content=content;
    }

    public static function cmp(a:Term,b:Term) {
        return a.content==b.content;
    }

    public function clone():Term {
        return new Term(""+content);
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
        this.executive.acts.push(new Pong1Act("^l", this, -0.1));
        this.executive.acts.push(new Pong1Act("^r", this, 0.1));

        this.executive.goalSystem.eternalGoals.push(new Term("c")); // try to keep in center
    }

    // returns the state of the world
    public function emitState(): Array<Term> {
        var res = [];

        var diff: Float = posX - posAlien;
        if (Math.abs(diff) < 0.1) {
            stateAsStr = "c";
            res.push(new Term("c"));
        }
        else if(diff > 0.0) {
            stateAsStr = "r";
            res.push(new Term("r"));
        }
        else {
            stateAsStr = "l";
            res.push(new Term("l"));
        }

        return res;
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
                    w.state.push(new Term('s$idx')); // shot down
                    w.posAliens[idx] = Math.random(); // respawn at random position

                    w.cntAliensHit++; // bump statistics
                    break; // break because the shot was absorbed by one alien and can't hit another
                }
            }
        }
    }
}

// TODO< add shooting action and goal to shoot down aliens >
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
        this.executive.acts.push(new Alien1Act("^l", this, -0.06));
        this.executive.acts.push(new Alien1Act("^r", this, 0.06));
        {
            var shootAct = new Alien1Act("^s", this, 0.0);
            shootAct.refractoryPeriod = 4; // don't let the agent spam the shot button
            this.executive.acts.push(shootAct);
        }

        this.executive.goalSystem.eternalGoals.push(new Term("s0")); // shoot down
        this.executive.goalSystem.eternalGoals.push(new Term("s1")); // shoot down
    }

    // returns the state of the world
    public function emitState(): Array<Term> {
        var res = state;

        stateAsStr = "";

        for(idx in 0...posAliens.length) {
            var diff: Float = posX - posAliens[idx];
            if (Math.abs(diff) < 0.1) {
                stateAsStr += ' c$idx';
                res.push(new Term('c$idx'));
            }
            else if(diff > 0.0) {
                stateAsStr += ' r$idx';
                res.push(new Term('r$idx'));
            }
            else {
                stateAsStr += ' l$idx';
                res.push(new Term('l$idx'));
            }
        }

        state = [];
        return res;
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
