/*
Copyright 2020 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

import sys.FileSystem;
import sys.io.File;
import sys.io.FileOutput;
import haxe.Int64;

// features:
// * anticipation
// * decision making: actions can have a refractory period to avoid spamming the environment with pointless actions
// * goal system: expectation and tree based goal system

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

    public function hasKey(key:Array<Term>): Bool {
        var keyComplete = ""+key.map(v -> TermUtils.convToStr(v));
        var tableResult = pairsByCond.get(keyComplete);
        return tableResult != null;
    }

    public function retByKey(key:Array<Term>): Array<Type> {
        var keyComplete = ""+key.map(v -> TermUtils.convToStr(v));
        return pairsByCond.get(keyComplete);
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



class ProceduralMemory {
    public var sizePairsOfProceduralNode = 50; // how many pairs are in a procedural node?

    public var pairs:Array<Pair> = []; // all known pairs, read only!
    // is extremely slow to iterate on!

    // procedural nodes
    public var proceduralNodes: ByCond<ProceduralNode> = new ByCond<ProceduralNode>();

    // maps conditions to the pairs which contain the condition
    // key is the string serialization of the parallel key terms as a string
    private var byCond:ByCond<Pair> = new ByCond<Pair>();

    public function new() {}

    public function addPair(pair:Pair) {
        pairs.push(pair);

        byCond.add(pair.condops[0].cond.events, pair);
        
        // add ProceduralNode by key if it doesn't yet exist
        if(!hasProceduralNodeByName(pair.condops[0].cond.events)) {
            proceduralNodes.add(pair.condops[0].cond.events, new ProceduralNode(pair.condops[0].cond.events));
        }

        { // add pair and keep under AIKR
            for(ipn in proceduralNodes.retByKey(pair.condops[0].cond.events)) {
                ipn.proceduralPairs.push(pair);

                // TODO< check ordering >
                ipn.proceduralPairs.sort((a, b) -> {
                    var aExp:Float = Tv.calcExp(a.calcFreq(), a.calcConf());
                    var bExp:Float = Tv.calcExp(b.calcFreq(), b.calcConf());
                    if (aExp > bExp) {
                        return 1;
                    }
                    if (aExp < bExp) {
                        return -1;
                    }
                    return 0;
                });
                ipn.limitSize(sizePairsOfProceduralNode);
            }
        }
    }

    // queries by conditional, either the complete parEvents or for single events (subset)
    public function queryPairsByCond(parEvents:Array<Term>): Array<Pair> {
        return byCond.queryByCond(parEvents);
    }

    private function hasProceduralNodeByName(name:Array<Term>) {
        return proceduralNodes.hasKey(name);
    }
}

// similar to node in ALANN, just for procedural knowledge
// a node in ALANN is similar to a concept, the adressing is just different
class ProceduralNode {
    public var name:Array<Term>; // name of the node

    // pairs, ordered by exp() to favor pairs which lead to better actions
    public var proceduralPairs:Array<Pair> = [];
    
    public function new(name) {
        this.name = name;
    }

    public function limitSize(size:Int) {
        proceduralPairs = proceduralPairs.slice(0, size);
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

    var queuedAct: Term = null;
    var queuedActOrigin: Pair = null; // origin of the queued action if it was done by the executive

    var trace:Array<Par> = [];

    public var randomActProb:Float = 0.0; // config - propability to do random action

    public var decisionThreshold:Float = 0.6; // config

    public var anticipationDeadline = 20; // config - anticipation deadline in cycles

    public var horizon5seq:Float = 8.0; // config - horizon for 5seq


    public var cycle:Int = 0; // global cycle timer

    public var dbgEvidence = false; // debugging - debug new and revised evidence?
    public var dbgAnticipationVerbose = false; // are anticipations verbose?

    public var dbgDescisionMakingVerbose = false; // debugging : is decision making verbose
    public var dbgExecVerbose = false; // debugging : is execution of ops verbose?

    public var mem = new ProceduralMemory();

    public function goalNow(g:Term) {
        // check and exec if it is a action
        if(tryDecomposeOpCall(g) != null) {
            execAct(g, null);
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
            if(Math.random() < randomActProb && queuedAct == null) { // do random action
                if (false) Sys.println('random act');
                
                var possibleActs = acts.filter(iAct -> iAct.act.refractoryPeriodCooldown <= 0); // only actions which are cooled down are possible as candidates

                var mass:Float = 0.0;
                for(iPossibleAct in possibleActs) {
                    mass += iPossibleAct.mass;
                }

                var selMass = Math.random()*mass;

                var massAccu = 0.0;
                for(idx in 0...possibleActs.length) {
                    // build queued act with the name and SELF arguments
                    var actName:String = possibleActs[idx].act.name;
                    var actTerm:Term = Cop("-->", Prod([Set("{", [Name("SELF")])]), Name(actName));

                    queuedAct = actTerm; // queue action as next action
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
            this.trace[0].events.push(queuedAct);
        }

        if (false) { // debug trace
            Sys.println('trace after queue insert');
            for(idx2 in 0...this.trace.length) {
                var idx = this.trace.length-1-idx2;
                Sys.println(' [$idx]  ${this.trace[idx].events.map(v -> TermUtils.convToStr(v))}');
            }
        }

        
        
        // helper function
        // do terms contain a action?
        function containsAction(terms:Array<Term>): Bool {
            return terms.filter(v -> tryDecomposeOpCall(v) != null).length > 0;
        }

        // helper function
        // aren't terms only actions?
        function containsAnyNonaction(terms:Array<Term>): Bool {
            return terms.filter(v -> !(tryDecomposeOpCall(v) != null)).length > 0;
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
            var candidatesByLocalChainedGoal: Array<{pair:Pair, tv:Tv, exp:Float}> = [
                for (iPair in candidates) {pair:iPair, tv:new Tv(iPair.calcFreq(), iPair.calcConf()),  exp:Tv.calcExp(iPair.calcFreq(), iPair.calcConf())}
            ];

            // * compute two op decision making candidates
            // ex: (&/, a, ^x, b, ^y) =/> c
            var enable5Seq = true; // are seq impl with 5 elements enabled? - costs a bit of performance
            var canditates5SeqByLocalChainedGoal: Array<{pair:Pair, tv:Tv, exp:Float}> = [];
            if(enable5Seq) {
                

                if (containsAnyNonaction(parEvents)) { // did candidate b just happen
                    // scan for ^x
                    var op0TraceIdx = -1; // -1 : not used
                    for(iOp0TraceIdxCandidate in 1...this.trace.length-1) {
                        if (containsAction(this.trace[iOp0TraceIdxCandidate].events)) {
                            op0TraceIdx = iOp0TraceIdxCandidate;
                            break;
                        }
                    }

                    if(op0TraceIdx != -1) { // is valid?
                        // scan for a
                        var cond0TraceIdx = -1;
                        for(iTraceIdx in op0TraceIdx+1...this.trace.length) {
                            if (containsAction(this.trace[iTraceIdx].events)) {
                                break; // break because we dont handle seq of multiple actions yet
                            }
                            if (containsAnyNonaction(this.trace[iTraceIdx].events)) {
                                cond0TraceIdx = iTraceIdx; // found it
                                break;
                            }
                        }

                        if (cond0TraceIdx != -1) {
                            // we are here if we found a candidate of a potential match in the trace
                            //
                            // now we need to check if we find a seq with these conditions in the database

                            var seq5potentialCond0 = this.trace[cond0TraceIdx].events;
                            var seq5potentialOp0 = this.trace[op0TraceIdx].events.filter(v -> tryDecomposeOpCall(v) != null)[0];
                            var seq5potentialCond1 = this.trace[0].events.filter(v -> !(tryDecomposeOpCall(v) != null));
                            var seq5potentialCandidates:Array<Pair> = mem.queryPairsByCond(seq5potentialCond0);                            
                            seq5potentialCandidates = seq5potentialCandidates.filter(iPair -> iPair.effect.events.filter(iEvent -> goalSystem.isEternalGoal(iEvent)).length > 0); // does it have a eternal goal as a effect?
                            seq5potentialCandidates = seq5potentialCandidates.filter(iPair -> !iPair.isConcurrentImpl && iPair.condops.length == 2);
                            seq5potentialCandidates = seq5potentialCandidates.filter(iPair -> iPair.condops[0].ops.length == 1 && TermUtils.equal(iPair.condops[0].ops[0], seq5potentialOp0)); // op of condops[0] must match up
                            seq5potentialCandidates = seq5potentialCandidates.filter(iPair -> Par.checkIntersect(iPair.condops[1].cond, new Par(seq5potentialCond1))); // condition must match up with observed one

                            // they are candidates for decision making if they match up!
                            canditates5SeqByLocalChainedGoal = [
                                for (iPair in seq5potentialCandidates) {pair:iPair, tv:new Tv(iPair.calcFreq(), iPair.calcConf()),  exp:Tv.calcExp(iPair.calcFreq(), iPair.calcConf())}
                            ];
                        }
                    }
                }

            }
            
            //commented because it is to slow
            //candidatesByLocalChainedGoal = filterCandidatesByGoal(candidates); // chain local pair -> matching goal in goal system
            
            var timeBefore2 = Sys.time();
            var candidatesByGoal: Array<{pair:Pair, tv:Tv, exp:Float}> = goalSystem.retDecisionMakingCandidatesForCurrentEvents(parEvents, parEvents);
            if(dbgDescisionMakingVerbose) Sys.println('descnMaking goal system time=${Sys.time()-timeBefore2}');

            var timeBefore3 = Sys.time();
            var candidatesFromForwardChainer1 = ForwardChainer.step(parEvents, 1, this);
            var candidatesFromForwardChainer2 = ForwardChainer.step(parEvents, 2, this);
            if(dbgDescisionMakingVerbose) Sys.println('descnMaking goal system forward chainer time=${Sys.time()-timeBefore3}');

            var candidates: Array<{pair:Pair, tv:Tv, exp:Float}> = candidatesByLocalChainedGoal
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
                    case Term.Cop("-->", _ , Name(n)): n;
                    default: throw "Invalid name!";
                }
            }

            var condOpsIdx = bestDecisionMakingCandidate.condops.length-1;
            if (bestDecisionMakingCandidate.condops[condOpsIdx].ops.length == 0) {
                throw "Assertion violated!";
            }

            if (
                bestDecisionExp > decisionThreshold && 
                retActByName(retName(bestDecisionMakingCandidate.condops[condOpsIdx].ops[0])).refractoryPeriodCooldown <= 0 // is it possible to execute the action based on refractory period?
            ) {
                queuedAct = bestDecisionMakingCandidate.condops[condOpsIdx].ops[0]; // queue action for next timestep
                queuedActOrigin = bestDecisionMakingCandidate;
            }
        }
        

        // * store sequences if possible
        {
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
                
                        var nonactionsOf2:Array<Term> = this.trace[iConditionCandidateIdx].events.filter(v -> !(tryDecomposeOpCall(v) != null));
                        var actionsOf1:Array<Term> = this.trace[traceIdxOfOpEvent].events.filter(v -> tryDecomposeOpCall(v) != null);
                        var nonactionsOf0:Array<Term> = this.trace[0].events.filter(v -> !(tryDecomposeOpCall(v) != null));
                        
                        {
                            for(iActionTerm in actionsOf1) { // iterate over all actions done at that time
                                if (dbgEvidence) {                            
                                    var stamp:Stamp = createStamp();
                                    var createdPair:Pair = new Pair(stamp);
                                    createdPair.condops = [new CondOps(new Par(nonactionsOf2), actionsOf1)];
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

                
                for(idxOp1 in 1...this.trace.length-1) {
                    if (containsAction(this.trace[idxOp1].events)) {
                        var traceIdxOfOpEvent = idxOp1;

                        scanBoundingEvntAndAddImplSeq(traceIdxOfOpEvent, hasMostRecentEventGoal);

                        function fn5() {
                            // search for 2nd op for building (&/, a, ^x, b, ^y) =/> c
                            
                            for(idxOp2 in idxOp1+1...this.trace.length-1) {
                                if (containsAction(this.trace[idxOp2].events)) {

                                    // search for event which was not action
                                    for(idxNop2 in idxOp2+1...this.trace.length) {
                                        if (containsAnyNonaction(this.trace[idxNop2].events)) {

                                            // we found a (&/, a, ^x, b, ^y) =/> c   candidate

                                            // scan for b candidates, add all as knowlede
                                            for(nonOp1Idx in idxOp1+1...idxOp2) {
                                                if (containsAnyNonaction(this.trace[nonOp1Idx].events)) {
                                                    
                                                    
                                                    var nonOpsOf2:Array<Term> = this.trace[idxNop2].events.filter(v -> !(tryDecomposeOpCall(v) != null)); // a
                                                    var opsOf2:Array<Term> = this.trace[idxOp2].events.filter(v -> tryDecomposeOpCall(v) != null); // ^x
                                                    var nonOpsOf1:Array<Term> = this.trace[nonOp1Idx].events.filter(v -> !(tryDecomposeOpCall(v) != null)); // b
                                                    var opsOf1:Array<Term> = this.trace[idxOp1].events.filter(v -> tryDecomposeOpCall(v) != null); // ^y
                                                    var nonOpsOf0:Array<Term> = this.trace[0].events.filter(v -> !(tryDecomposeOpCall(v) != null)); // c

                                                    // try to add to knowledge
                                                    {
                                                        // TODO< add different combinations of event, par event, op, etc >

                                                        var condOps:Array<CondOps> = [new CondOps(new Par(nonOpsOf2), [opsOf2[0]]), new CondOps(new Par(nonOpsOf1), [opsOf1[0]])];
                                                        addEvidence2(condOps, nonOpsOf0, createStamp(), false, horizon5seq);
                                                    }
                                                }
                                            }

                                            return; // break up search
                                        }
                                    }
                                }
                            }
                        }

                        
                        fn5();
                        

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

    // helper function to check if a term is a operation call and to decompose it into name and arguments
    // returns null if it is not a operation call
    public static function tryDecomposeOpCall(term:Term):{name:String, args:Array<Term>} {
        switch term {
            case Term.Cop("-->", Term.Prod(args), Term.Name(name)) if (name.length > 0 && name.charAt(0) == '^'):
            return {name:name, args:args};
            case _:
            return null;
        }
    }

    // TODO< replace with addEvidence2() >
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
                (isConcurrentImpl ? true : TermUtils.equal(iPair.condops[0].ops[0], iActionTerm)) &&
                Par.checkSubset(iPair.condops[0].cond, new Par(conds)) // TODOOPTIMIZE< is not necessary >
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
                (isConcurrentImpl ? true : TermUtils.equal(iPair.condops[0].ops[0], iActionTerm)) &&
                Par.checkSame(iPair.condops[0].cond, new Par(conds)) // TODOOPTIMIZE< is not necessary >
            ) {
                if (Par.checkSame(iPair.effect, new Par(effects))) {
                    existsEvidence = true;
                }
            }
        }

        if (!existsEvidence) { // create new evidence if it doesn't yet exist
            
            // store pair
            var createdPair:Pair = new Pair(stamp);

            var ops = iActionTerm != null ? [iActionTerm] : [];
            createdPair.condops = [new CondOps(new Par(conds), ops)];
            createdPair.effect = new Par(effects);
            createdPair.isConcurrentImpl = isConcurrentImpl;

            if(dbgEvidence) trace('create new evidence ${createdPair.convToStr()}');

            mem.addPair(createdPair); ///pairs.push(createdPair);
        }
    }




    // adds new evidence
    // /param iActionTerm is the action term which is used for checking and, can be null if isConcurrentImpl is true
    private function addEvidence2(condOps:Array<CondOps>, effects:Array<Term>, stamp:Stamp, isConcurrentImpl, horizon:Float) {
        for (iCondOps in condOps) {
            if (Par.checkIntersect(iCondOps.cond, new Par(effects))) {
                return; // exclude (&/, a, ^b) =/> a
            }
        }
        

        for(iPair in mem.queryPairsByCond(condOps[0].cond.events)) { // search for existing evidence and try to revise
            if (
                iPair.isConcurrentImpl == isConcurrentImpl &&
                iPair.condops.length == condOps.length &&
                Par.checkSubset(iPair.effect, new Par(effects))
            ) {
                var isSame = true;                
                for (iCondOpsIdx in 0...condOps.length) {
                    if (
                        (isConcurrentImpl && condOps[iCondOpsIdx].ops.length > 0 ? true : TermUtils.equal(iPair.condops[iCondOpsIdx].ops[0], condOps[iCondOpsIdx].ops[0])) &&
                        Par.checkSubset(iPair.condops[iCondOpsIdx].cond, condOps[iCondOpsIdx].cond) // TODOOPTIMIZE< is not necessary >
                    ) {}
                    else {
                        isSame = false;
                        break; // optimization
                    }
                }

                if (isSame) {
                    iPair.evidenceCnt++;
                    iPair.evidencePositive++;
                }
            }
        }

        var existsEvidence = false; // does exact evidence exist?
        
        for(iPair in mem.queryPairsByCond(condOps[0].cond.events)) { // search for exact evidence
            if (
                iPair.isConcurrentImpl == isConcurrentImpl &&
                iPair.condops.length == condOps.length &&
                Par.checkSame(iPair.effect, new Par(effects)) // TODOOPTIMIZE< is not necessary >
            ) {

                var isSame = true;                
                for (iCondOpsIdx in 0...condOps.length) {
                    if (
                        (isConcurrentImpl && condOps[iCondOpsIdx].ops.length > 0 ? true : TermUtils.equal(iPair.condops[iCondOpsIdx].ops[0], condOps[iCondOpsIdx].ops[0])) &&
                        Par.checkSame(iPair.condops[iCondOpsIdx].cond, condOps[iCondOpsIdx].cond) 
                    ) {}
                    else {
                        isSame = false;
                        break; // optimization
                    }
                }

                if (isSame) {
                    existsEvidence = true;
                }
            }
        }
        

        if (!existsEvidence) { // create new evidence if it doesn't yet exist
            
            // store pair
            var createdPair:Pair = new Pair(stamp);
            createdPair.condops = condOps;
            createdPair.effect = new Par(effects);
            createdPair.isConcurrentImpl = isConcurrentImpl;
            createdPair.horizon = horizon;

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
        }

        return res;
    }

    function retActByName(actName:String): Act {
        return acts.filter(iAct -> iAct.act.name == actName)[0].act;
    }

    // realize action
    // /param origin origin of the action, used for anticipation , can be null
    function execAct(actTerm:Term, origin:Pair) {
        if(dbgExecVerbose) Sys.println('ACT ${TermUtils.convToStr(actTerm)} origin = ${origin != null ? origin.convToStr() : "null"}');

        // extract arguments and name of op
        var args:Array<Term> = null; // arguments
        var actName:String = null;
        switch actTerm {
            case Cop("-->", Prod(args2), Name(actName2)):
            actName = actName2;
            args = args2;
            case _:
            if (dbgExecVerbose)  Sys.println('   ... action has invalid format, ignore');
            return; // invalid format of act
        }

        // lookup action and call handler
        var act = retActByName(actName);
        act.refractoryPeriodCooldown = act.refractoryPeriod;
        act.exec(args);

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
    public function sample(time:Int): ActiveGoal {
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
    public function retDecisionMakingCandidatesForCurrentEvents(parEvents: Array<Term>, currentEvents: Array<Term>): Array<{pair:Pair, tv:Tv, exp:Float}> {
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
                    return Par.checkSubset(iPair.effect, node.sourcePair.condops[0].cond);
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
                    nodesByCond.add(createdChildren.sourcePair.condops[0].cond.events, createdChildren);
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
                
                if (Math.random() < terminationProbability) {
                    return; // terminate
                }

                // do the same recursivly
                if (node.children.length == 0) {
                    return;
                }
                // pick random children
                var idx = Std.random(node.children.length);
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
                var idx = Std.random(elementsOfTree.length);
                selectedNode = elementsOfTree[idx];
            }

            tryAdd(selectedNode);
        }
    }

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

            Logger.log('$space$nodeInfoStr');

            for(iChildren in node.children) {
                debugTreeRec(iChildren, depth+1);
            }
        }

        Logger.log('t=${executive.cycle}  goal tree:');
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

                Logger.log('goal system  #treeNodes=$nTreeNodes');
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

    public override function sample(time:Int): ActiveGoal {
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
                add = Par.checkSubset(node.sourcePair.condops[0].cond, pair.effect);
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

    public override function retDecisionMakingCandidatesForCurrentEvents(parEvents: Array<Term>, currentEvents: Array<Term>): Array<{pair:Pair, tv:Tv, exp:Float}> {
        var resultArr = [];

        {
            var candidateNodes:Array<PlanningTreeNode> = nodesByCond.queryByCond(parEvents)
                .filter(v -> !v.sourcePair.isConcurrentImpl) // only allow =/>
                .filter(ipTreeNode -> { // consider only candidates which fullfill not satisfied goals
                    if(ipTreeNode.sourcePair != null && Par.checkIntersect( ipTreeNode.sourcePair.effect, new Par(currentEvents))) {
                        return false; // don't consider as candidate because the effects are already happening
                    }
                    
                    if(ipTreeNode.parent != null && ipTreeNode.parent.sourcePair != null) {
                        if(Par.checkIntersect( ipTreeNode.parent.sourcePair.effect, new Par(currentEvents))) {
                            return false; // don't consider as candidate because the effects are already happening
                        }
                    }
                    return true;
                });
            
            for(iCandidateNode in candidateNodes) {
                var tv = iCandidateNode.retTv(null);
                var exp:Float = Tv.calcExp(tv.freq, tv.conf);
                resultArr.push({pair:iCandidateNode.sourcePair, tv:tv, exp:exp});
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
    public static function step(currentEvents:Array<Term>, chainDepth:Int, exec:Executive): Array<{pair:Pair, tv:Tv, exp:Float}> {
        // sample the current events and try to chain to a goal

        if (currentEvents.length == 0) {
            return []; // nothing to sample
        }


        var idx:Int = Std.random(currentEvents.length);
        var selChainEvent: Term = currentEvents[idx]; // select event to try to chain
        var chainTv: Tv = new Tv(1.0, 0.99999); // tv of chaining - assumed to be axiomatic

        var chain: Array<Term> = [selChainEvent]; // chain of events
        var combinedStamp: Stamp = exec.createStamp(); // TODO< get stamp from selected event ! >

        var chain2 = [];

        for(iChainDepth in 0...chainDepth) {
            var firstChainElementCandidate:Array<Pair> = exec.mem.pairs.filter(
                iPair ->
                    iPair.condops[0].cond.hasEvent(selChainEvent) &&
                    !Par.checkIntersect(iPair.effect, new Par(currentEvents)) && // don't consider as candidate because the effects are already happening
                    !iPair.isConcurrentImpl // can't be concurrent because it leads to wrong plans and we only care about actionable seq impl
            );
            
            // sample first chain element candidate
            if (firstChainElementCandidate.length == 0) {
                return []; // nothing to sample
            }



            var selChainPair0Idx:Int = Std.random(firstChainElementCandidate.length);
            var selChainPair0: Pair = firstChainElementCandidate[selChainPair0Idx];

            chain2.push(selChainPair0);

            if (Stamp.checkOverlap(selChainPair0.stamp, combinedStamp)) {
                return []; // we don't allow stamp overlap!
            }
            combinedStamp = Stamp.merge(combinedStamp, selChainPair0.stamp);

            selChainEvent = selChainPair0.effect.events[0]; // TODO< select any event >
            chainTv = Tv.induction(chainTv, new Tv(selChainPair0.calcFreq(), selChainPair0.calcConf()));

            for(iOp in selChainPair0.condops[0].ops) {
                chain.push(iOp);
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

            hitGoal = hitGoal ||
                exec.goalSystem.retDecisionMakingCandidatesForCurrentEvents([selChainEvent], currentEvents).length > 0; // did we hit a derived goal?

            if (!hitGoal) {
                return []; // because we derived something which doesn't hit a goal, it's pointless!
            }
        }

        // we are only here if we hit a goal with the chained effect

        // "destinations" of chained goal
        var chainDests = exec.goalSystem.retDecisionMakingCandidatesForCurrentEvents([selChainEvent], currentEvents);
        
        return [
            for (iChainDest in chainDests) {
                var dedTv = Tv.deduction(chainTv, iChainDest.tv);
                {
                pair: chain2[0], // return only first chain element because our plan starts with it
                tv:dedTv,
                exp:dedTv.exp()};
            }
        ];
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

// sequence of condition and ops, ops are a sequence
class CondOps {
    public var cond:Par = null;
    public var ops:Array<Term> = [];

    public function new(cond, ops) {
        this.cond = cond;
        this.ops = ops;
    }
}

class Pair {
    public var condops:Array<CondOps> = []; // array of sequence of conditions and operations

    //public var cond:Par = null;
    //public var act:Array<Term> = []; // TODO< rename to ops >
    
    public var effect:Par = null;

    public var evidencePositive = 1; // positive evidence counter
    public var evidenceCnt = 1; // evidence counter

    public var stamp:Stamp;

    public var isConcurrentImpl = false; // is it =|> instead of =/> ?

    public var horizon:Float = 1.0; // horizon for conf computation

    public function new(stamp) {
        this.stamp = stamp;
    }

    public function calcConf() {
        // see http://alumni.media.mit.edu/~kris/ftp/Helgason%20et%20al-AGI2013.pdf
        return evidenceCnt / (evidenceCnt + horizon);
    }

    public function calcFreq() {
        var p:Float = evidencePositive;
        return p / evidenceCnt;
    }

    public function convToStr():String {
        if (isConcurrentImpl) {
            return '${condops[0].cond.events.map(v -> TermUtils.convToStr(v))} =|> ${effect.events.map(v -> TermUtils.convToStr(v))} {${calcFreq()} ${calcConf()}} // cnt=$evidenceCnt';
        }
        
        var seq = [];
        for(iCondOp in condops) {
            seq.push('${iCondOp.cond.events.map(v -> TermUtils.convToStr(v))}');
            seq.push('${iCondOp.ops.map(v -> TermUtils.convToStr(v))}');
        }

        return '(&/, ${seq.join(",")}) =/> ${effect.events.map(v -> TermUtils.convToStr(v))} {${calcFreq()} ${calcConf()}} // cnt=$evidenceCnt';
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

    /*abstract*/public function exec(args:Array<Term>) {
        throw "NOT IMPLEMENTED!";
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

class Logger {
    public static var singleton = new Logger();
    
    public var f:FileOutput;

    public function new() {
        var logName:String = "logX.log";
        if (FileSystem.exists(logName)) {
            FileSystem.deleteFile(logName); // delete old file
        }
        f = File.append(logName);
    }

    public static function log(text:String) {
        Logger.singleton.log2(text);
    }

    private function log2(text:String) {
        f.writeString(text+"\n");
        f.flush();
    }
}





// TODO LATER< terms can act like neurons and send spikes to other terms, some spikes can add up with ded for seq spikes >
