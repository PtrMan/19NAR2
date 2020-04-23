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

class ProceduralMemory {
    public var sizePairsOfProceduralNode = 50; // how many pairs are in a procedural node?

    public var proceduralNodes: Map<String, ProceduralNode> = new Map<String, ProceduralNode>(); // by string of term of name of ProceduralNode

    public function new() {}

    // TODO< rename to addImplSeq() >
    public function addPair(implSeq:ImplSeq) {
        // enumerate all terms where we have to try to add the ImplSeq
        var containedTerms:Array<Term> = [];
        {
            // we need to add events of condops
            for (iCondOp in implSeq.condops) {
                for (iEvent in iCondOp.cond.events) {
                    containedTerms.push(iEvent);
                }
            }

            // we need to add pred event of ImplSeq
            for (iEvent in implSeq.effect.events) {
                containedTerms.push(iEvent);
            }
        }

        // helper to create procedural node if it doesn't exist by name. tries to add implSeq to the implSeq node by name.
        // /param name name to add implSeq to
        function tryAddImplSeqToProceduralNodes(name:Term) {
            var nameAsStr:String = TermUtils.convToStr(name);
            
            // add new node if node doesn't exist
            if (!proceduralNodes.exists(nameAsStr)) {
                var createdNode = new ProceduralNode(name);
                proceduralNodes.set(nameAsStr, createdNode);
            }
            
            // try to add to node
            var selNode:ProceduralNode = proceduralNodes.get(nameAsStr);

            // only add if it doesn't exist already
            // * try to find it
            for (iImplSeq in selNode.implSeqs) {
                if (ImplSeq.checkSameByTerm(iImplSeq, implSeq)) {
                    return; // found it -> no need to add
                }
            }

            // * add it
            selNode.implSeqs.push(implSeq);

            // keep under AIKR
            // TODO< check if ordering is correct >
            selNode.implSeqs.sort((a, b) -> {
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
            selNode.limitSize(sizePairsOfProceduralNode);
        }

        // try add implSeq to node by name
        for (iName in containedTerms) {
            tryAddImplSeqToProceduralNodes(iName);
        }
    }

    // queries by conditional, either the complete parEvents or for single events (subset)
    public function queryPairsByCond(parEvents:Array<Term>): Array<ImplSeq> {
        if (parEvents.length == 0) {
            return []; // should never happen!
        }

        var res = [];

        // * query of all parallel events
        if (proceduralNodes.exists(TermUtils.convToStr(parEvents[0]))) { // we can query parallel events by first event
            var selNode = proceduralNodes.get(TermUtils.convToStr(parEvents[0]));
            // select all where first event matches 
            res = res.concat(
                selNode.implSeqs.filter(iImplSeq -> Par.checkSame(iImplSeq.condops[0].cond, new Par(parEvents))));
        }

        // * query for each single event
        for(iSelEvent in parEvents) {
            var selNode = proceduralNodes.get(TermUtils.convToStr(parEvents[0]));
            if (selNode != null) {
                // select all where first event matches 
                res = res.concat(
                    selNode.implSeqs.filter(iImplSeq -> Par.checkSame(iImplSeq.condops[0].cond, new Par([iSelEvent]))));
            }
        }

        return res;
    }

    // queries by single event predicate
    // usually used for backward inference (goal derivation)
    public function queryByPredicate(pred:Term): Array<ImplSeq> {
        var selNode = proceduralNodes.get(TermUtils.convToStr(pred));
        if (selNode == null) {
            return [];
        }
        // TODO?< do we need to select by subset of Par? >
        return selNode.implSeqs.filter(iImplSeq -> Par.checkSame(iImplSeq.effect, new Par([pred])));
    }
}

// similar to node in ALANN, just for procedural knowledge
// a node in ALANN is similar to a concept, the adressing is just different
class ProceduralNode {
    public var name:Term; // name of the node

    // ImplSeq's, ordered by exp() to favor ImplSeq's which lead to better actions
    public var implSeqs:Array<ImplSeq> = [];
    
    public function new(name) {
        this.name = name;
    }

    public function limitSize(size:Int) {
        implSeqs = implSeqs.slice(0, size);
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
    var queuedActOrigin: ImplSeq = null; // origin of the queued action if it was done by the executive

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

    public var decl:Nar.Declarative = null; // declarative part of the reasoner

    public function goalNow(g:Term) {
        // check and exec if it is a action
        if(tryDecomposeOpCall(g) != null) {
            execAct(g, null);
        }

        // record to trace
        this.trace[0].events.push(g);
    }

    // converts a impl seq to the real representation
    public function inputJudgement(term:Term, tv:Tv) {
        function isOp(term:Term) {
            return switch (term) {
                case Term.Cop("-->", Term.Prod(_), Term.Name(name)) if (name.length > 0 && name.charAt(0) == "^"): true;
                case _: false;
            }
        }

        switch (term) {
            case Term.Cop("=/>", Term.Compound("&/", [seq0, op1]), pred) if(isOp(op1)): // match for impl seq
            
            // build impl seq
            var implSeq = new ImplSeq(createStamp());
            implSeq.effect = new Par([pred]);
            implSeq.condops = [new CondOps(new Par([seq0]), [op1])];
            mem.addPair(implSeq);

            case _:
            trace('Executive.inputJugdgement() expected (term &/ op) =/> x. !');
            // ignore term
        }
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
        var bestDecisionMakingCandidate:ImplSeq;
        { // select best decision making candidate
            
            var timeBefore = Sys.time();
            
            
            var candidates:Array<ImplSeq> = [];// candidates for decision making in this step
            // * compute candidates for decision making in this step
            candidates = mem.queryPairsByCond(parEvents)
                .filter(iPair -> iPair.effect.events.filter(iEvent -> goalSystem2.isGoalByTerm(iEvent)).length > 0) // does it have a eternal goal as a effect?
                .filter(v -> !v.isConcurrentImpl); /////pairs.filter(v -> Par.checkSubset(new Par(parEvents), v.cond));
            
            // (&/, a, ^op) =/> b  where b!
            var candidatesByLocalChainedGoal: Array<{pair:ImplSeq, tv:Tv, exp:Float}> = [
                for (iPair in candidates) {pair:iPair, tv:new Tv(iPair.calcFreq(), iPair.calcConf()),  exp:Tv.calcExp(iPair.calcFreq(), iPair.calcConf())}
            ];

            // * compute two op decision making candidates
            // ex: (&/, a, ^x, b, ^y) =/> c
            var enable5Seq = true; // are seq impl with 5 elements enabled? - costs a bit of performance
            var canditates5SeqByLocalChainedGoal: Array<{pair:ImplSeq, tv:Tv, exp:Float}> = [];
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
                            var seq5potentialCandidates:Array<ImplSeq> = mem.queryPairsByCond(seq5potentialCond0);                            
                            seq5potentialCandidates = seq5potentialCandidates.filter(iPair -> iPair.effect.events.filter(iEvent -> goalSystem2.isGoalByTerm(iEvent)).length > 0); // does it have a eternal goal as a effect?
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
            var candidatesByGoal: Array<{pair:ImplSeq, tv:Tv, exp:Float}> = goalSystem2.retDecisionMakingCandidatesForCurrentEvents(parEvents);
            if(dbgDescisionMakingVerbose) Sys.println('descnMaking goal system time=${Sys.time()-timeBefore2}');

            var timeBefore3 = Sys.time();
            ///var candidatesFromForwardChainer1 = ForwardChainer.step(parEvents, 1, this);
            ///var candidatesFromForwardChainer2 = ForwardChainer.step(parEvents, 2, this);
            if(dbgDescisionMakingVerbose) Sys.println('descnMaking goal system forward chainer time=${Sys.time()-timeBefore3}');

            var candidates: Array<{pair:ImplSeq, tv:Tv, exp:Float}> = candidatesByLocalChainedGoal
                .concat(candidatesByGoal)
                ///.concat(candidatesFromForwardChainer1)
                ///.concat(candidatesFromForwardChainer2)
                ;
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
                var hasMostRecentEventGoal = parEvents.filter(iEvent -> goalSystem2.isGoalByTerm(iEvent)).length > 0;


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
                                    var createdPair:ImplSeq = new ImplSeq(stamp);
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
        goalSystem2.step(this); // let the goal system manage eternal goals etc
        goalSystem2.goalDerivation(this);

        if (cycle % 101 == 0) {
            goalSystem2.limitMemory();
        }

        goalSystem2.currentTime = cycle;

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
            
            // store ImplSeq
            var createdPair:ImplSeq = new ImplSeq(stamp);

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
            var createdPair:ImplSeq = new ImplSeq(stamp);
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
    function filterCandidatesByGoal(candidates:Array<ImplSeq>):Array<{pair:ImplSeq, exp:Float}> {
        var res = [];
        for(iCandi in candidates) {
            // add it to the decision making candidates if it is a candidate
            ///OLD CODE 21.03.2020
            ///var tv:Tv = goalSystem.retDecisionMakingCandidateTv(iCandi); 
            var tv:Tv = goalSystem2.retDecisionMakingCandidateTv(iCandi.effect.events);
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
    function execAct(actTerm:Term, origin:ImplSeq) {
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
    public function selBestAct(candidates:Array<{pair:ImplSeq, exp:Float}>): ImplSeq {
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

    // used to submit a goal
    public function submitGoalByTerm(goalTerm:Term, tv:Tv) {
        goalSystem2.submitGoalByTerm(goalTerm, tv, createStamp(), cycle);
    }

    public var anticipationsInflight:Array<InflightAnticipation> = []; // anticipations in flight

    ///public var goalSystem:AbstractGoalSystem = new TreePlanningGoalSystem();

    // new goal system
    public var goalSystem2:GoalSystem = new GoalSystem(); 

    // TODO< should be Int64 >
    public var stampCounter:Int = 1; // counter for the creation of new stamps
}




// the used goal system
class GoalSystem {
    // importance sampled by currentTime-creationTime * exp()
    public var activeGoals:Array<ActiveGoal2> = [];
    
    public var decayrate:Float = 0.0003; // decay rate of the goals

    public var currentTime:Int = 0; // must be updated by executive!

    public function new() {}

    
    // returns the TV of the goal of the effect of the pair, returns null if it doesn't lead to a goal
    public function retDecisionMakingCandidateTv(effects:Array<Term>):Tv {
        var bestGoal:ActiveGoal2 = null;
        
        for(iGoal in activeGoals) {
            if( iGoal.condOps.ops.length == 0 ) { // must have no ops
                if (iGoal.condOps.cond.events.length == 1) { // must be a single event which is the goal
                    if (TermUtils.equal(iGoal.condOps.cond.events[0], effects[0])) { // is the term the same? // TODO< check for subset of par >
                        if (bestGoal == null) {
                            bestGoal = iGoal;
                        }
                        else {
                            if (iGoal.tv.exp() > bestGoal.tv.exp()) {
                                bestGoal = iGoal;
                            }
                        }
                    }
                }
            }
        }

        if (bestGoal == null) {
            return null;
        }
        return bestGoal.tv;
    }

    // returns the candidates for decision making which match to current events as a precondition together with exp()
    public function retDecisionMakingCandidatesForCurrentEvents(currentEvents: Array<Term>): Array<{pair:ImplSeq, tv:Tv, exp:Float}> {
        // retDecisionMakingCandidatesForCurrentEvents() is not implemented!
        return [];
    }

    public function submitGoalByTerm(goalTerm:Term, tv:Tv, stamp:Stamp, currentTime2:Int) {
        Sys.println('[d] submitted goal by term ${TermUtils.convToStr(goalTerm)} ${tv.convToStr()}');

        var goalCondOp:CondOps = new CondOps(new Par([goalTerm]), []);

        var goal:ActiveGoal2 = new ActiveGoal2(goalCondOp, tv, stamp, currentTime);
        submitGoal2(goal);
    }

    // used to submit a new goal
    public function submitGoal2(goal:ActiveGoal2) {
        // debug
        Sys.println('[d] submitted goal ${ExecUtils.convCondOpToStr(goal.condOps)}');

        // look for goal with same term and reset time and tv if found
        for(iGoal in activeGoals) {
            if (CondOps.checkSame(iGoal.condOps, goal.condOps)) {
                if (goal.creationTime > iGoal.creationTime) {
                    iGoal.creationTime = goal.creationTime;
                    iGoal.tv = goal.tv;
                }

                return; // found, we don't need to add goal
            }
        }

        activeGoals.push(goal);
    }

    // checks if term is a goal
    public function isGoalByTerm(t:Term) {
        for(iGoal in activeGoals) {
            if( iGoal.condOps.ops.length == 0 ) { // must have no ops
                if (iGoal.condOps.cond.events.length == 1) { // must be a single event which is the goal
                    if (TermUtils.equal(iGoal.condOps.cond.events[0], t)) { // is the term the same?
                        return true;
                    }
                }
            }
        }
        return false;
    }

    public function step(exec:Executive) {
        var sampledGoal:ActiveGoal2 = sample(exec.cycle);
        if (sampledGoal == null) {
            return;
        }
        processGoal(sampledGoal, exec.decl);
    }

    // derives new goals
    public function goalDerivation(exec:Executive) {
        var sampledGoal:ActiveGoal2 = sample(exec.cycle);
        if (sampledGoal == null) {
            return;
        }

        if (sampledGoal.condOps.ops.length == 0) { // we only handle the cond ops without ops for now
            Sys.println('[d] goalsystem: GOAL DERIVATION');

            var selGoalEvent:Term = sampledGoal.condOps.cond.events[0]; // select first event of par events
            Sys.println('[d] goalsystem: sel goal = '+TermUtils.convToStr(selGoalEvent)+"!");

            var matchingImplSeqs:Array<ImplSeq> = exec.mem.queryByPredicate(selGoalEvent);
            for(iMatchedImplSeq in matchingImplSeqs) {
                Sys.println('[d] goalsystem: matching impl seq = '+iMatchedImplSeq.convToStr());
            }

            // we need to derive goals from matching implSeqs by goal deduction
            // a =/> b.
            // b!
            // |- ded
            // a!
            for(iImplSeq in matchingImplSeqs) {
                var tvCompound = new Tv(iImplSeq.calcFreq(), iImplSeq.calcConf());
                var tvComponent = sampledGoal.tv;
                var tvConcl = Tv.deduction(tvCompound, tvComponent);
                
                var stampConcl = Stamp.merge(sampledGoal.stamp, iImplSeq.stamp);
                
                // TODO< we need to deal with multiple condops! >
                var goal:ActiveGoal2 = new ActiveGoal2(iImplSeq.condops[0], tvConcl, stampConcl, sampledGoal.creationTime);
                submitGoal2(goal);
            }
        }
        else { // case with ops
            {
                // (a &/ ^x)!
                // |- DesireDed (deduction)   (structural deduction)
                // a!
                var condOpsConcl = new CondOps(sampledGoal.condOps.cond, []); // split off ops
                var tvConcl = Tv.structDeduction(sampledGoal.tv);
                
                var goal:ActiveGoal2 = new ActiveGoal2(condOpsConcl, tvConcl, sampledGoal.stamp, sampledGoal.creationTime);
                submitGoal2(goal);
            }
        }
    }

    public function sample(time:Int): ActiveGoal2 {
        if (activeGoals.length == 0) {
            return null; // didn't find any goal
        }

        var mass:Float = 0.0;
        for(iGoal in activeGoals) {
            mass += calcRelativePri(iGoal, time);
        }


        // probabilistic selection
        var selectedMass = Math.random()*mass;
        var accu = 0.0;

        for(iGoal in activeGoals) {
            accu += calcRelativePri(iGoal, time);
            if (accu >= selectedMass) {
                return iGoal;
            }
        }
        return activeGoals[activeGoals.length-1];
    
    }
    


    // called when a goal was selected and when it should get realized
    public function processGoal(selGoal:ActiveGoal2, decl:Nar.Declarative) {
        // handling for ^d declarative special op
        // is used to query declarative knowledge for procedural inference
        if (!selGoal.qaWasQuestedAlready) {
            if (selGoal.condOps.ops.length == 1) { // we only handle condops with length 1 for now
                var opNameAndArgs:{name:String, args:Array<Term>} = Executive.tryDecomposeOpCall(selGoal.condOps.ops[0]);
                if (opNameAndArgs != null && opNameAndArgs.name == "^d") { // is valid ^d declarative pseudo op?
                    // we assume that arg[0] is always {SELF}
                    
                    var questionTerm:Term = opNameAndArgs.args[1];
    
                    // ask question and register answer handler for it
                    var handler = new DeclarativeAnswerHandler(selGoal, this);
                    decl.question(questionTerm, handler);
                    
                    selGoal.qaWasQuestedAlready = true; // we had now asked a question to handle this goal
                }
            }
        }
    }

    // helper to decompose ^d of pseudo-op to return question Term
    // returns null if invalid
    public static function retOpDQuestionTerm(goal:ActiveGoal2): Term {
        if (goal.condOps.ops.length == 1) { // we only handle condops with length 1 for now
            var opNameAndArgs:{name:String, args:Array<Term>} = Executive.tryDecomposeOpCall(goal.condOps.ops[0]);
            if (opNameAndArgs != null && opNameAndArgs.name == "^d") { // is valid ^d declarative pseudo op?
                // we assume that arg[0] is always {SELF}
                
                var questionTerm:Term = opNameAndArgs.args[1];
                return questionTerm;
            }
        }
        return null;
    }

    public function limitMemory() {
        var maxGoals = 1000;

        activeGoals.sort( (a, b) -> (calcRelativePri(a, currentTime) < calcRelativePri(b, currentTime) ? 1 : ((calcRelativePri(a, currentTime) == calcRelativePri(b, currentTime)) ? 0 : -1) ));
        activeGoals = activeGoals.slice(0, maxGoals); // keep under AIKR
    }

    // helper to compute the relative priority of a goal
    private function calcRelativePri(activeGoal:ActiveGoal2, time:Int): Float {
        var timediff = time-activeGoal.creationTime;
        var decay = Math.exp(-decayrate*timediff);
        return decay*Tv.calcExp(activeGoal.tv.freq, activeGoal.tv.conf);
    }
}

// Q&A handler to handler answer to ^d question and to create a new goal with the unified variables
class DeclarativeAnswerHandler implements Nar.AnswerHandler2 {
    public var goalSystem:GoalSystem;
    public var goal:ActiveGoal2; // goal for which the question was derived to handle the ^d pseudo-op

    public function new(goal:ActiveGoal2, goalSystem:GoalSystem) {
        this.goal = goal;
        this.goalSystem = goalSystem;
    }
    
    public function report(sentence:Nar.Sentence, cycles:Int):Void {
        Sys.println('[d] decl answer handler called for ^d');

        // unify to compute asignment of variables
        
        var origTerm:Term = GoalSystem.retOpDQuestionTerm(goal); // return term of ^d pseudo-op

        // unify variables
        var unfiedMap = new Map<String, Term>();
        var wasUnified = Nar.Unifier.unify(sentence.term, origTerm, unfiedMap);
        if (!wasUnified) {
            // should have been unified
            return; // internal error, ignore
        }

        // derive goal with unified variables and add goal !
        var cond:Par = goal.condOps.cond;
        var substParEventTerms:Array<Term> = cond.events.map(iCondTerm -> Nar.Unifier.substitute(iCondTerm, unfiedMap, "#")); // substitute variables in par
        var derivCondPar:Par = new Par(substParEventTerms);

        var derivCondOp:CondOps = new CondOps(derivCondPar, []);

        { // debug
            Sys.println('[d] derived goal ${ExecUtils.convCondOpToStr(derivCondOp)}');
        }

        // * create derived goal
        var derivedGoal:ActiveGoal2 = new ActiveGoal2(derivCondOp, goal.tv, goal.stamp, goalSystem.currentTime);

        // * register goal
        goalSystem.submitGoal2(derivedGoal);
    }
}

// declarative pseudo-op
// ( <#y --> z>   &/ < ({SELF} * ($x, #y) --> x) --> ^d > ) =/> <$x --> goal>.

class ActiveGoal2 {
    public var condOps:CondOps;
    public var tv:Tv;
    public var stamp:Stamp;
    public var creationTime:Int; // creation time in cycles

    public var qaWasQuestedAlready:Bool = false; // was a question already submitted to the declarative inference for ^d special op?

    public function new(condOps, tv, stamp, creationTime) {
        this.condOps = condOps;
        this.tv = tv;
        this.stamp = stamp;
        this.creationTime = creationTime;
    }
}

class ExecUtils {
    public static function convCondOpToStr(condops:CondOps):String {
        var parEventsAsStr:Array<String> = condops.cond.events.map(iTerm -> TermUtils.convToStr(iTerm));
        var opsAsStr:Array<String> = condops.ops.map(iTerm -> TermUtils.convToStr(iTerm));

        var res:String = "";

        // convert eventually parallel/seq events to string
        function concatTermStr(ts:Array<String>, connector:String):String {
            if(ts.length == 0) {
                return "";
            }
            if(ts.length == 1) {
                return ts[0];
            }
            var res2 = "";
            for(iTs in ts) {
                res2 += iTs+" "+connector+" ";
            }
            res.substr(0, res.length-2-connector.length);
            return '( $res )';
        }

        var parEventsAsStr2 = concatTermStr(parEventsAsStr, "&|");
        var opsAsStr2 = concatTermStr(opsAsStr, "&/");
        return '($parEventsAsStr2 &/ $opsAsStr2)';
    }
}









// anticipated event which is anticipated because a action was done which leads to some anticipated effect
class InflightAnticipation {
    public var origin:ImplSeq; // origin of the anticipation: ex: (&/, a, ^b) =/> c
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

    public static function checkSame(a:CondOps, b:CondOps):Bool {
        if (!Par.checkSame(a.cond,b.cond)) {
            return false;
        }
        if (a.ops.length!=b.ops.length) {
            return false;
        }
        for(idx in 0...a.ops.length) {
            if (!TermUtils.equal(a.ops[idx], b.ops[idx])) {
                return false;
            }
        }
        return true;
    }
}

class ImplSeq {
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

    // check if it represents the same equivalent term
    public static function checkSameByTerm(a:ImplSeq, b:ImplSeq):Bool {
        if(a.isConcurrentImpl != b.isConcurrentImpl) { // must have same copula
            return false;
        }
        if(!Par.checkSame(a.effect, b.effect)) {
            return false;
        }
        if (a.condops.length != b.condops.length) {
            return false;
        }
        for(idx in 0...a.condops.length) {
            if (!CondOps.checkSame(a.condops[idx], b.condops[idx])) {
                return false;
            }
        }

        return true;
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
    public static var singleton:Logger;// = new Logger();
    
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
