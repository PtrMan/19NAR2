/*
Copyright 2020 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

import haxe.Int64;

class ProceduralMemory {
    public var sizePairsOfProceduralNode = 50; // how many pairs are in a procedural node?

    public var proceduralNodes: Map<String, ProceduralNode> = new Map<String, ProceduralNode>(); // by string of term of name of ProceduralNode

    public function new() {}

    // TODO< rename to addImplSeq() >
    public function addPair(implSeq:ImplSeq,exec:Executive) {
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
                if (ImplSeq.checkSameByTerm(iImplSeq, implSeq)) { // is only the same if te term and timing is the same!
                    if (exec.enExponentialIntervals) {
                        var isInChunk = Executive.exponentialIntervals_checkSameChunk(iImplSeq.dtEffect, implSeq.dtEffect);
                        if(isInChunk) {
                            return; // found it -> no need to add
                        }
                    }
                    else {
                        if(iImplSeq.dtEffect == implSeq.dtEffect) {
                            return; // found it -> no need to add
                        }
                    }
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

        var resMap:Map<String, ImplSeq> = new Map<String, ImplSeq>(); // we need a map to make sure that we add each result just once

        // * query of all parallel events
        if (proceduralNodes.exists(TermUtils.convToStr(parEvents[0]))) { // we can query parallel events by first event
            var selNode = proceduralNodes.get(TermUtils.convToStr(parEvents[0]));
            // select all where first event matches 
            var resCandidates =
                selNode.implSeqs.filter(iImplSeq -> Par.checkSame(iImplSeq.condops[0].cond, new Par(parEvents)));
            for(iCandidate in resCandidates) {
                if(!resMap.exists(iCandidate.convToStr())) {
                    resMap.set(iCandidate.convToStr(), iCandidate);
                }
            }
        }

        // * query for each single event
        for(iSelEvent in parEvents) {
            var selNode = proceduralNodes.get(TermUtils.convToStr(parEvents[0]));
            if (selNode != null) {
                // select all where first event matches 
                var resCandidates =
                    selNode.implSeqs.filter(iImplSeq -> Par.checkSame(iImplSeq.condops[0].cond, new Par([iSelEvent])));
                for(iCandidate in resCandidates) {
                    if(!resMap.exists(iCandidate.convToStr())) {
                        resMap.set(iCandidate.convToStr(), iCandidate);
                    }
                }
            }
        }

        var res = [];
        for(i in resMap.keyValueIterator()) {
            res.push(i.value);
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


class Trace {
    public var trace:Array<TraceItem> = [];

    public var traceMaxLength = 20; // max length of trace in events/timesteps (depends on implementation)
    
    public function new() {}

    public function append(v:TraceItem) {
        trace.push(v);
        if(trace.length > traceMaxLength) {
            trace = trace.slice(1);
        }
    }

    // sample one sequence from the trace
    // doesn't filter for valid sequences!
    public function sample():Array<TraceItem> {
        var seqLen = 3; // length of sequence

        if (this.trace.length < seqLen) {
            return []; // not enough
        }

        var openIndices=[for (i in 0...this.trace.length) i];
        var pickedIndices = [];
        for(it in 0...seqLen-1) {
            var pickedIdxIdx = Std.random(openIndices.length-1);
            var pickedIdx = openIndices[pickedIdxIdx];
            openIndices.remove(pickedIdx);
            pickedIndices.push(pickedIdx);
        }
        // add last index to force to add last event
        // we can do this because we call sample() every timestep
        pickedIndices.push(trace.length-1);

        var res = pickedIndices.map(idx -> this.trace[idx]);
        res.sort((a, b) -> a.t - b.t); // necessary because indices may not be in order!
        
        // debug
        //trace('Trace.sample() returned');
        //for(iv in res) {
        //    trace('  ${iv.t}');
        //}

        return res;
    }
}

// item in a trace
class TraceItem {
    public var t:Int; // absolute time of event

    public var events:Array<Term>; // events which happened at that time

    public function new(events:Array<Term>, t:Int) {
        this.events = events;
        this.t = t;
    }
}



class Executive {
    
    //commented because it is in memory    public var pairs:Array<Pair> = []; // all known pairs

    public var acts:Array<{mass:Float, act:Act}> = []; // list of all actions
    
    public function new() {
        depthFirstPlanner.exec = this; // wire executive to planner
    }

    var queuedAct: Term = null;
    var queuedActOrigins: Array<ImplSeq> = []; // origins of the queued action if it was done by the executive

    public var trace2:Trace = new Trace();

    //public var trace:Array<Par> = [];
    //public var traceMaxLength = 20; // max length of trace in events/timesteps (depends on implementation)
    //public var horizon5seq:Float = 8.0; // config - horizon for 5seq


    public var randomActProb:Float = 0.0; // config - propability to do random action

    public var decisionThreshold:Float = 0.6; // config

    public var anticipationDeadline = 20; // config - anticipation deadline in cycles


    public var cycle:Int = 0; // global cycle timer

    public var dbgEvidence = false; // debugging - debug new and revised evidence?
    public var dbgAnticipationVerbose = false; // are anticipations verbose?

    public var dbgDescisionMakingVerbose = false; // debugging : is decision making verbose
    public var dbgExecVerbose = false; // debugging : is execution of ops verbose?

    public var mem = new ProceduralMemory();

    public var decl:Nar.Declarative = null; // declarative part of the reasoner

    // config - deadline algorithm
    // "dt2plus" - compute deadline by interval*2 + slack, similar to 'OpenNARS for Research'
    // "const"   - take constant deadline, good for crisp environments where a clear deadline makes sense
    public var deadlineAlgorithm:String = "const";

    /* commented because outdated, we pass ops to be executed with different API
    public function goalNow(g:Term) {
        // check and exec if it is a action
        if(tryDecomposeOpCall(g) != null) {
            execAct(g, null);
        }

        // record to trace
        this.trace[0].events.push(g);
    }
    */

    public var enDepthFirstPlanner:Bool = false; // enable depth first planner? - flag necessary because it is experimental and leads currently to contradictary goals in natural environments such as pong1 and pong2
    public var depthFirstPlanner:DepthFirstPlanner = new DepthFirstPlanner(); // COMPONENT - planner which is used to search for depth first goals
    
    // used to submit a goal by input
    public function submitGoalByTerm(goalTerm:Term, tv:Tv) {
        goalSystem2.submitGoalByTerm(this, goalTerm, tv, createStamp(), cycle, EnumSentenceSource.INPUT);
    }


    public function submitEventGoal(term:Term, tv:Tv) {
        function isOp(term:Term) {
            return switch (term) {
                case Term.Cop("-->", Term.Prod(_), Term.Name(name,_)) if (name.length > 0 && name.charAt(0) == "^"): true;
                case _: false;
            }
        }

        if (isOp(term)) {
            queuedAct = term; // queue to execute action
        }
        else {
            submitGoalByTerm(term, tv);
        }
    }

    // converts a impl seq to the real representation
    public function submitEternalJudgement(term:Term, tv:Tv) {
        function isOp(term:Term) {
            return switch (term) {
                case Term.Cop("-->", Term.Prod(_), Term.Name(name,_)) if (name.length > 0 && name.charAt(0) == "^"): true;
                case _: false;
            }
        }

        switch (term) {
            case Term.Cop("=/>", Term.Compound("&/", [seq0, op1]), pred) if(isOp(op1)): // match for impl seq
            
            // build impl seq
            var implSeq = new ImplSeq(createStamp());
            implSeq.effect = new Par([pred]);
            implSeq.condops = [new CondOps(new Par([seq0]), [op1])];
            // TODO< we need to revise correctly! >
            mem.addPair(implSeq,this);

            case _:
            trace('Executive.inputJugdgement() expected (term &/ op) =/> x. !');
            // ignore term
        }
    }

    public var msgsOfDebug:Array<String> = []; // collected debug messages

    public var parEvents:Array<Term> = []; // current parallel events, is used to accumulate events which happen in one frame/instant

    public function step() {
        if (enDepthFirstPlanner) {
            depthFirstPlanner.step(); // give time to depth first planner
        }

        // * "neutralize" fullfilled goals
        for (iEvent in parEvents) {
            goalSystem2.submitEvent(iEvent);
        }

        var buildParConjunctions = false; // build parallel conjunction?
                                          // disabled because it's unnecessary

        if (buildParConjunctions) {
            // * add evidence of parallel events
            //   builds a =|> b  b =|> a  from parEvents=[a, b]
            if (parEvents.length > 1) {
                // TODO< sample ba random if there are to many events >
                for(idxA in 0...parEvents.length) for(idxB in 0...parEvents.length) {
                    var stamp = createStamp();
                    addEvidence([parEvents[idxA]], 0, [parEvents[idxB]], stamp, null, true);
                    addEvidence([parEvents[idxB]], 0, [parEvents[idxA]], stamp, null, true);
                }
            }
        }


        // * try to confirm anticipations
        anticipationTryConfirm(parEvents);

        // * store events to trace
        if (parEvents.length > 0) {
            trace2.append(new TraceItem(parEvents, cycle));
        }

        // commented because this code is outdated because trace got refactored
        //if (false) { // debug trace
        //    Dbg.dbg(true, 'trace');
        //    for(idx2 in 0...this.trace.length) {
        //        var idx = this.trace.length-1-idx2;
        //        Dbg.dbg(true, ' [$idx]  ${this.trace[idx].events.map(v -> TermUtils.convToStr(v))}');
        //    }
        //}

        { // do random action
            if(Math.random() < randomActProb && queuedAct == null) { // do random action
                Dbg.dbg(false, 'random act');
                
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
                    var actTerm:Term = Cop("-->", Prod([Set("{", [Name("SELF",false)])]), Name(actName,false));

                    queuedAct = actTerm; // queue action as next action
                    queuedActOrigins = []; // has no origin because it was done by random

                    massAccu += possibleActs[idx].mass;
                    if (massAccu > selMass) {
                        break;
                    }
                }

                //commented because old code
                //var idx=Std.random(possibleActs.length);
                //queuedAct = possibleActs[idx].act.name; // queue action as next action
                //queuedActOrigins = []; // has no origin because it was done by random
            }
        }
        
        if (queuedAct != null) {
            execAct(queuedAct, queuedActOrigins);

            // record to trace
            var add = false; // add new event time to trace?
            if (trace2.trace.length > 0) {
                add = trace2.trace[trace2.trace.length-1].t != cycle; // were events recorded in a different cycle?
            }
            else {
                add = true;
            }

            if (add) {
                trace2.append(new TraceItem([queuedAct], cycle));
            }
            else {
                // we need to add it to the last trace item
                // assert(trace2.trace[trace2.trace.length-1].t == cycle)
                trace2.trace[trace2.trace.length-1].events.push(queuedAct);
            }
        }
        
        // commented because this code is outdated because trace got refactored
        //if (false) { // debug trace
        //    Dbg.dbg(true, 'trace after queue insert');
        //    for(idx2 in 0...this.trace.length) {
        //        var idx = this.trace.length-1-idx2;
        //        Dbg.dbg(true,' [$idx]  ${this.trace[idx].events.map(v -> TermUtils.convToStr(v))}');
        //    }
        //}

        
        
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
        queuedActOrigins = [];
        var bestDecisionMakingCandidate:ImplSeq = null;



        // select best decision making candidate by NAL classical inference
        // we do this by filtering the goals by current event and consider matching events of the seq by ded
        {
            // list of candidates eligable for decision making
            // desire: the computed desire with the current parallel events
            var decisionCandidates3:Array<{desire:Tv, originGoal:ActiveGoal2}> = [];

            var sw = Stopwatch.createAndStart();
            
            // for all single events
            for(iCurrentEvent in parEvents) {
                for(iMatchingGoal in goalSystem2.retByMatchingFirstEvent(new Par([iCurrentEvent])).filter(igoal -> igoal.condOps.ops.length > 0)/*must have ops*/) {
                    var desire:Tv = ruleOpDeduction(iMatchingGoal.desire, new Tv(1.0, 0.998)); // compute tv of conclusion by ded
                    decisionCandidates3.push({desire:desire,originGoal:iMatchingGoal});
                }
            }

            // for parallel occuring events
            {
                for(iMatchingGoal in goalSystem2.retByMatchingFirstEvent(new Par(parEvents)).filter(igoal -> igoal.condOps.ops.length > 0)/*must have ops*/) {
                    var desire:Tv = ruleOpDeduction(iMatchingGoal.desire, new Tv(1.0, 0.998)); // compute tv of conclusion by ded
                    decisionCandidates3.push({desire:desire,originGoal:iMatchingGoal});
                }
            }

            if (decisionCandidates3.length > 0) { // are there any candidates for decision making?
                // NOTE< we select first op for now!, TODO< we actually need to queue up ops! > >
                var bestDecisionCandidate:{condOps:CondOps, opTerm:Term, desire:Tv} = {condOps:decisionCandidates3[0].originGoal.condOps, opTerm:decisionCandidates3[0].originGoal.condOps.ops[0], desire:decisionCandidates3[0].desire};
                for(iCandidate in decisionCandidates3) {
                    if(iCandidate.desire.exp() > bestDecisionCandidate.desire.exp()) {
                        // NOTE< we select first op for now!, TODO< we actually need to queue up ops! > >
                        bestDecisionCandidate = {condOps:iCandidate.originGoal.condOps, opTerm:iCandidate.originGoal.condOps.ops[0], desire:iCandidate.desire};
                    }
                }

                if (bestDecisionCandidate.desire.exp() > decisionThreshold) {
                    var origins:Array<ImplSeq> = [];
                    
                    //COMMENTED BECAUSE OLD CODE IS USING IT AND WE DONT USE OLD CODE!   queuedAct = bestDecisionCandidate.opTerm;

                    Dbg.dbg(true, 'DescnMaking: found best decision candidate, query possible anticipations for '+ExecUtils.convCondOpToStr(bestDecisionCandidate.condOps));

                    // query all impl seq's where the condOps match,
                    // we need this for anticipation like
                    //    happened: (a &/ ^opX).
                    //    need to anticipate all effects of matching impl seq like ex:
                    //        (a &/ ^opX) =/> z.
                    //        (a &/ ^opX) =/> sx.
                    // TODO LATER LOW< we do handle only candidates with one condops, how to generalize it to more? >
                    var matchingImplSeq = mem.queryPairsByCond(parEvents).filter(iImplSeq -> iImplSeq.condops.length == 1 && CondOps.checkSame(iImplSeq.condops[0], bestDecisionCandidate.condOps));
                    for (iMatchingImplSeq in matchingImplSeq) {
                        // add origins of decision for later anticipation
                        origins.push(iMatchingImplSeq);
                    }

                    execAct(bestDecisionCandidate.opTerm, origins);

                }
            }

            var dt:Float = sw.retCurrentTimeDiff();
            Dbg.dbg(dbgDescisionMakingVerbose,'descnMaking classical time=$dt');
        }


        // select best decision making candidate
        
        if (bestDecisionMakingCandidate != null) {
            var bestDecisionExp:Float = Tv.calcExp(bestDecisionMakingCandidate.calcFreq(), bestDecisionMakingCandidate.calcConf());
            
            if (dbgDescisionMakingVerbose) trace('decsn making $bestDecisionExp > $decisionThreshold');
            
            // helper function to return name
            function retName(t:Term):String {
                return switch(t) {
                    case Term.Cop("-->", _ , Name(n,_)): n;
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
                queuedActOrigins = [bestDecisionMakingCandidate];
            }
        }
        

        // * store sequences if possible
        {
            var traceSamples:Int = 3; // how many samples are drawn from the trace in every step to build impl seq?

            for(iSample in 0...traceSamples) {
                var implSeqCandidate:Array<TraceItem> = trace2.sample();
                if (implSeqCandidate.length == 0) {
                    continue; // is not valid
                }

                // case for len=3
                if (implSeqCandidate.length == 3) {
                    var first = implSeqCandidate[0];
                    var mid = implSeqCandidate[1];
                    var last = implSeqCandidate[2];

                    // is any event of the most recent events a goal?
                    var hasMostRecentEventGoal = last.events.filter(iEvent -> goalSystem2.isGoalByTerm(iEvent)).length > 0;
                    if (hasMostRecentEventGoal) { // must have last event as a goal
                        
                        var nonactionsOf2:Array<Term> = first.events.filter(v -> !(tryDecomposeOpCall(v) != null));
                        var actionsOf1:Array<Term> = mid.events.filter(v -> tryDecomposeOpCall(v) != null);
                        var nonactionsOf0:Array<Term> = last.events.filter(v -> !(tryDecomposeOpCall(v) != null));
                        
                        var dtEffect:Int = last.t-mid.t; // compute dt

                        if (nonactionsOf0.length > 0 && actionsOf1.length > 0 && nonactionsOf2.length > 0) {
                            for(iActionTerm in actionsOf1) { // iterate over all actions done at that time
                                
                                msgsOfDebug.push('sampled');


                                var stamp:Stamp = createStamp();

                                addEvidence(nonactionsOf2, dtEffect, nonactionsOf0, stamp, iActionTerm, false);
                                
                                // add evidence of combinations of single events of cond and effect
                                if (nonactionsOf2.length > 1) {
                                    for(iCond in nonactionsOf2) {
                                        addEvidence([iCond], dtEffect, nonactionsOf0, stamp, iActionTerm, false);
                                    }
                                }

                                if (nonactionsOf0.length > 1) {
                                    for(iEffect in nonactionsOf0) {
                                        addEvidence(nonactionsOf2, dtEffect, [iEffect], stamp, iActionTerm, false);
                                    }
                                }
                                
                                if (nonactionsOf2.length > 1 && nonactionsOf0.length > 1) {
                                    for(iCond in nonactionsOf2) {
                                        for (iEffect in nonactionsOf0) {
                                            addEvidence([iCond], dtEffect, [iEffect], stamp, iActionTerm, false);
                                        }
                                    }
                                }
                            }    
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

        parEvents = []; // reset accumulator of current parallel events
    }

    // //{Event (&/,a,op())!, Event a.} |- Event op()!
    public static function ruleOpDeduction(compoundTv:Tv,componentTv:Tv):Tv {
        return Tv.deduction(compoundTv, componentTv);
    }

    // helper function to check if a term is a operation call and to decompose it into name and arguments
    // returns null if it is not a operation call
    public static function tryDecomposeOpCall(term:Term):{name:String, args:Array<Term>} {
        switch term {
            case Term.Cop("-->", Term.Prod(args), Term.Name(name,_)) if (name.length > 0 && name.charAt(0) == '^'):
            return {name:name, args:args};
            case _:
            return null;
        }
    }

    // enable "exponential intervals"?
    // the basic idea is to divide the time-intervals before the pred of a impl seq into exponential sized "chunks" and account for the evidence for each chunk seperatlyy
    public var enExponentialIntervals:Bool = true; // config

    // adds new evidence
    // /param iActionTerm is the action term which is used for checking and, can be null if isConcurrentImpl is true
    private function addEvidence(conds:Array<Term>, dtEffect:Int, effects:Array<Term>, stamp:Stamp, iActionTerm:Term, isConcurrentImpl) {
        addEvidence2([new CondOps(new Par(conds), [iActionTerm])], dtEffect, effects, stamp, isConcurrentImpl, 1.0);
    }

    // adds new evidence
    // /param iActionTerm is the action term which is used for checking and, can be null if isConcurrentImpl is true
    // /param horizon horizon for conf computation
    private function addEvidence2(condOps:Array<CondOps>, dtEffect:Int, effects:Array<Term>, stamp:Stamp, isConcurrentImpl, horizon:Float) {
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

                    //Sys.println(iPair.condops[iCondOpsIdx].ops.length);
                    //Sys.println(condOps[iCondOpsIdx].ops.length);

                    //Sys.println(iPair.condops[iCondOpsIdx].ops[0]);
                    //Sys.println(condOps[iCondOpsIdx].ops[0]);

                    // concurrent case
                    if (isConcurrentImpl) {
                        if (!Par.checkSubset(iPair.condops[iCondOpsIdx].cond, condOps[iCondOpsIdx].cond)) { // TODOOPTIMIZE< is not necessary >)                        
                            isSame = false;
                            break; // optimization
                        }
                    }
                    else { // sequential case
                        /* commented because wrong and because this case is to complicated and not necessary
                        else if (!isConcurrentImpl) {
                            if( iPair.condops[iCondOpsIdx].ops.length > 0 &&
                            condOps[iCondOpsIdx].ops.length > 0 && 
                            TermUtils.equal(iPair.condops[iCondOpsIdx].ops[0], condOps[iCondOpsIdx].ops[0])) &&
                        Par.checkSubset(iPair.condops[iCondOpsIdx].cond, condOps[iCondOpsIdx].cond)) // TODOOPTIMIZE< is not necessary >
                            {}
                        }
                        */
                    }
                }

                var isInChunk = enExponentialIntervals ? false : true;
                if (enExponentialIntervals) {
                    isInChunk = exponentialIntervals_checkSameChunk(dtEffect, iPair.dtEffect);
                }

                if(isSame) { // only account for evidence if it is in the same chunk
                    if(isInChunk) {
                        iPair.evidenceCnt++;
                        iPair.evidencePositive++;
                    }
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

                    //Sys.println(iPair.condops[iCondOpsIdx].ops.length);
                    //Sys.println(condOps[iCondOpsIdx].ops.length);

                    //Sys.println(iPair.condops[iCondOpsIdx].ops[0]);
                    //Sys.println(condOps[iCondOpsIdx].ops[0]);

                    // concurrent case
                    if (isConcurrentImpl) {
                        if (!Par.checkSubset(iPair.condops[iCondOpsIdx].cond, condOps[iCondOpsIdx].cond)) { // TODOOPTIMIZE< is not necessary >)                        
                            isSame = false;
                            break; // optimization
                        }
                    }
                    else { // sequential case
                        /* commented because wrong and because this case is to complicated and not necessary
                        else if (!isConcurrentImpl) {
                            if( iPair.condops[iCondOpsIdx].ops.length > 0 &&
                            condOps[iCondOpsIdx].ops.length > 0 && 
                            TermUtils.equal(iPair.condops[iCondOpsIdx].ops[0], condOps[iCondOpsIdx].ops[0])) &&
                        Par.checkSubset(iPair.condops[iCondOpsIdx].cond, condOps[iCondOpsIdx].cond)) // TODOOPTIMIZE< is not necessary >
                            {}
                        }
                        */
                    }
                }

                if (isSame) {
                    var isInChunk = enExponentialIntervals ? false : true;
                    if (enExponentialIntervals) {
                        isInChunk = exponentialIntervals_checkSameChunk(dtEffect, iPair.dtEffect);
                    }

                    if (isInChunk) {
                        existsEvidence = true;
                    }
                }
            }
        }
        

        if (!existsEvidence) { // create new evidence if it doesn't yet exist
            
            // store pair
            var createdPair:ImplSeq = new ImplSeq(stamp);
            createdPair.condops = condOps;
            createdPair.dtEffect = dtEffect;
            createdPair.effect = new Par(effects);
            createdPair.isConcurrentImpl = isConcurrentImpl;
            createdPair.horizon = horizon;

            if(dbgEvidence) trace('create new evidence ${createdPair.convToStr()}');

            mem.addPair(createdPair,this);
        }
    }

    // checks if the intervals fall into the same range acording to the "exponential interval" criterion
    public static function exponentialIntervals_checkSameChunk(aDt:Int, bDt:Int): Bool {
        function calcRange(dt:Int):Int {
            for(iRange in 0...10) {
                var exponent = 1.7;
                var max = Std.int(Math.pow(iRange, exponent));
                if (dt <= max) {
                    return iRange;
                }
            }
            return 10; // is in "infinite" large range
        }
        return calcRange(aDt)==calcRange(bDt);
    }

    // decrements the remaining refractory period
    private function decisionmakingActionCooldown() {
        for (iAct in acts) {
            iAct.act.refractoryPeriodCooldown--;
        }
    }

    // emits neg-confirm if anticipation didn't occur
    private function anticipationMaintainNegAnticipations() {
        Dbg.dbg(true, 'ANTICIPATION cnt = ${anticipationsInflight.length}');
        
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
            var tvComponent:Tv = goalSystem2.retDecisionMakingCandidateTv(iCandi.effect.events);
            if (tvComponent != null) {
                var tv:Tv = Tv.deduction(new Tv(iCandi.calcFreq(), iCandi.calcConf()), tvComponent); // goal deduction

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
    // /param origin origin of the action, used for anticipation , can be empty
    function execAct(actTerm:Term, origins:Array<ImplSeq>) {
        Dbg.dbg(dbgExecVerbose, '[d ] exec: ACT ${TermUtils.convToStr(actTerm)}');
        //if(dbgExecVerbose) Sys.println('[d ] exec:     origins = ${origins.map(io -> io.convToStr()}');


        // extract arguments and name of op
        var args:Array<Term> = null; // arguments
        var actName:String = null;
        switch actTerm {
            case Cop("-->", Prod(args2), Name(actName2,_)):
            actName = actName2;
            args = args2;
            case _:
            Dbg.dbg(dbgExecVerbose,'   ... action has invalid format, ignore');
            return; // invalid format of act
        }

        // lookup action and call handler
        var act = retActByName(actName);
        act.refractoryPeriodCooldown = act.refractoryPeriod;
        act.exec(args);

        for(iOrigin in origins) {
            anticipationGenerate(iOrigin, false);
        }
    }

    // generate a anticipation
    // /param origin can be null, origin of the anticipation, ex: (a &/ ^opX) =/> b
    public function anticipationGenerate(origin:ImplSeq, addIfExisting:Bool) {
        if (origin != null) {
            var deadline:Int = anticipationDeadline;
            if (deadlineAlgorithm == "dt2plus") { // is our deadline algorithm dt*2 + deadlineSlack , simular to the one done in 'OpenNARS for Research'?
                var deadlineSlack:Int = 5;    
                deadline = origin.dtEffect*2 + deadlineSlack;
            }

            if (!addIfExisting) {
                // check if anticipation is already present
                for (iaif in anticipationsInflight) {
                    if (ImplSeq.checkSameByTerm(iaif.origin, origin)) {
                        return; // don't add anticipation with same origin
                    }
                }

            }
            
            // add anticipation
            Dbg.dbg(true, 'ANTICIPATION: anticipate ${origin.convToStr()} deadline +$deadline');
            
            anticipationsInflight.push(new InflightAnticipation(origin, cycle + deadline));
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

    public function retJudgements(): Array<String> {
        var res=[];

        var allJudgements:Map<String, Bool> = new Map<String, Bool>();

        for (iProcNode in mem.proceduralNodes) {
            for (iImplSeq in iProcNode.implSeqs) {
                allJudgements.set(iImplSeq.convToStr(), true);
            }
        }

        for (iJudgementStr in allJudgements.keys()) {
            res.push(iJudgementStr);
        }

        return res;
    }

    public function debugJudgements() {
        for (iJudgementStr in retJudgements()) {
            Dbg.dbg(true,iJudgementStr);
        }
    }

    // helper to create stamp
    public function createStamp():Stamp {
        return new Stamp([Int64.make(0, stampCounter++)], new StructuralOriginsStamp([]));
    }

    public var anticipationsInflight:Array<InflightAnticipation> = []; // anticipations in flight

    ///public var goalSystem:AbstractGoalSystem = new TreePlanningGoalSystem();

    // new goal system
    public var goalSystem2:GoalSystem = new GoalSystem(); 

    // TODO< should be Int64 >
    public var stampCounter:Int = 1; // counter for the creation of new stamps
}

// enum for queryy if effect is the same and in the same range
enum EnumEffectRange {
    INSAMERANGE;
    NOTINSAMERANGE;
    NOTSAME; // effect is not the same
}


// the used goal system
class GoalSystem {
    // importance sampled by currentTime-creationTime * exp()
    public var activeGoals:Array<ActiveGoal2> = [];
    
    public var decayrate:Float = 0.0003; // decay rate of the goals

    public var currentTime:Int = 0; // must be updated by executive!

    public var debugGoalSystem:Bool = false;

    public var goaltableSize:Int = 30;

    public var realizedThreshold:Float = 0.9*0.5; // setting - threshold to realize a goal

    public var enGoalDetachment:Bool = false; // do we enable goal detachment?, disabled because current version has control problems

    public function new() {}

    // filter goals by first event
    public function retByMatchingFirstEvent(par:Par): Array<ActiveGoal2> {
        return activeGoals.filter(iActiveGoal -> Par.checkSame(iActiveGoal.condOps.cond, par));
    }
    
    // returns the TV of the goal of the effect of the pair, returns null if it doesn't lead to a goal
    public function retDecisionMakingCandidateTv(effects:Array<Term>):Tv {
        var bestGoal:ActiveGoal2 = null;
        
        for(iGoal in activeGoals) {
            // is eligable by desire?
            // we don't want to realize goals with to low desire!
            var desireThreshold:Float = 0.1;
            if (iGoal.desire.exp() < desireThreshold) {
                continue; // ignore
            }
            
            if( iGoal.condOps.ops.length == 0 ) { // must have no ops
                if (iGoal.condOps.cond.events.length == 1) { // must be a single event which is the goal
                    if (TermUtils.equal(iGoal.condOps.cond.events[0], effects[0])) { // is the term the same? // TODO< check for subset of par >
                        if (iGoal.calcRealized() > realizedThreshold) {
                            continue; // don't realize already realized goals
                        }
                        
                        if (bestGoal == null) {
                            bestGoal = iGoal;
                        }
                        else {
                            if (iGoal.desire.exp() > bestGoal.desire.exp()) {
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
        return bestGoal.desire;
    }

    // returns the candidates for decision making which match to current events as a precondition together with exp()
    public function retDecisionMakingCandidatesForCurrentEvents(currentEvents: Array<Term>): Array<{pair:ImplSeq, tv:Tv, exp:Float}> {
        // retDecisionMakingCandidatesForCurrentEvents() is not implemented!
        return [];
    }

    public function submitGoalByTerm(executive:Executive, goalTerm:Term, tv:Tv, stamp:Stamp, currentTime2:Int, source:EnumSentenceSource) {
        Dbg.dbg(debugGoalSystem, 'submitted goal by term ${TermUtils.convToStr(goalTerm)} ${tv.convToStr()}');

        var goalCondOp:CondOps = new CondOps(new Par([goalTerm]), []);

        var goal:ActiveGoal2 = new ActiveGoal2(goalCondOp, tv, stamp, currentTime);
        submitGoal2(executive, goal, source);
    }

    // used to submit a new goal
    public function submitGoal2(executive:Executive, goal:ActiveGoal2, source:EnumSentenceSource) {
        { // submit goal to depth first planner
            executive.depthFirstPlanner.submitGoal(goal, 1.0);
        }
        
        var store = true; // do we want to store the goal additionally?
                          // is required to keep goals up to date, old not important or outdated goals will get pushed out of memory!
        
        // debug
        Dbg.dbg(debugGoalSystem, 'submitted goal ${ExecUtils.convCondOpToStr(goal.condOps)}! source ${source}');

        // look for goal with same term and reset time and tv if found
        for(iGoal in activeGoals) {
            if (CondOps.checkSame(iGoal.condOps, goal.condOps)) {
                if(source == EnumSentenceSource.INPUT) { // favor input goals
                    if (goal.creationTime > iGoal.creationTime) {
                        iGoal.desire = goal.desire; // we need to reset desire too!!!
                        iGoal.creationTime = goal.creationTime;
                        iGoal.stamp = goal.stamp;
                    }
    
                    return; // found, we don't need to add goal
                }

                var isOverlap = Stamp.checkOverlap(goal.stamp, iGoal.stamp);

                if (isOverlap) {
                    if (goal.desire.exp() > iGoal.desire.exp()) { // choice rule
                        iGoal.stamp = goal.stamp;
                        iGoal.desire = goal.desire; // we need to reset desire too!!!
                        iGoal.creationTime = goal.creationTime;
                    }
                    store = true; // still store it
                    break; // fall through to store goal
                }
                else {
                    // goal revision
                    iGoal.stamp = Stamp.merge(iGoal.stamp, goal.stamp);
                    iGoal.desire = Tv.revision(iGoal.desire, goal.desire);
                    store = true; // still store it
                    break;
                }
            }
        }

        if (store) {
            activeGoals.push(goal);
        }
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
        processGoal(sampledGoal, exec.decl, exec);
    }

    // derives new goals
    public function goalDerivation(exec:Executive) {
        var sampledGoal:ActiveGoal2 = sample(exec.cycle);
        if (sampledGoal == null) {
            return;
        }

        //var realizedThreshold:Float = 0.9;
        //if (sampledGoal.calcRealized() > realizedThreshold) {
        //    return; // don't realize already realized goals
        //}

        if (sampledGoal.condOps.ops.length == 0) {
            Dbg.dbg(debugGoalSystem, 'goalsystem: GOAL DERIVATION');

            var selGoalEvent:Term = sampledGoal.condOps.cond.events[0]; // select first event of par events
            Dbg.dbg(debugGoalSystem, 'goalsystem: sel goal = '+TermUtils.convToStr(selGoalEvent)+"!");

            var matchingImplSeqs:Array<ImplSeq> = exec.mem.queryByPredicate(selGoalEvent);
            for(iMatchedImplSeq in matchingImplSeqs) {
                Dbg.dbg(debugGoalSystem, 'goalsystem: matching impl seq = '+iMatchedImplSeq.convToStr());
            }

            // we need to derive goals from matching implSeqs by goal deduction
            // a =/> b.
            // b!
            // |- ded
            // a!
            for(iImplSeq in matchingImplSeqs) {
                var tvCompound = new Tv(iImplSeq.calcFreq(), iImplSeq.calcConf());
                var tvComponent = sampledGoal.desire;
                var tvConcl = Tv.deduction(tvCompound, tvComponent);
                
                var stampConcl = Stamp.merge(sampledGoal.stamp, iImplSeq.stamp);
                
                // TODO< we need to deal with multiple condops! >
                var goal:ActiveGoal2 = new ActiveGoal2(iImplSeq.condops[0], tvConcl, stampConcl, sampledGoal.creationTime);
                submitGoal2(exec, goal, EnumSentenceSource.DERIVED);
            }
        }
        else { // case with ops
            {
                if (sampledGoal.condOps.cond.events.length > 0 && enGoalDetachment) { // must have cond events!
                    // (a &/ ^x)!
                    // |- DesireDed (deduction)   (structural deduction)
                    // a!
                    var condOpsConcl = new CondOps(sampledGoal.condOps.cond, []); // split off ops
                    var desireConcl = Tv.structDeduction(sampledGoal.desire);
                    
                    var goal:ActiveGoal2 = new ActiveGoal2(condOpsConcl, desireConcl, sampledGoal.stamp, sampledGoal.creationTime);
                    submitGoal2(exec, goal, EnumSentenceSource.DERIVED);
                }
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
    public function processGoal(selGoal:ActiveGoal2, decl:Nar.Declarative, exec:Executive) {
        // handling for ^d declarative special op
        // is used to query declarative knowledge for procedural inference
        if (!selGoal.qaWasQuestedAlready) {
            if (selGoal.condOps.ops.length == 1) { // we only handle condops with length 1 for now
                var opNameAndArgs:{name:String, args:Array<Term>} = Executive.tryDecomposeOpCall(selGoal.condOps.ops[0]);
                if (opNameAndArgs != null && opNameAndArgs.name == "^d") { // is valid ^d declarative pseudo op?
                    // we assume that arg[0] is always {SELF}
                    
                    var questionTerm:Term = opNameAndArgs.args[1];
    
                    // ask question and register answer handler for it
                    var handler = new DeclarativeAnswerHandler(exec, selGoal, this);
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
        activeGoals.sort( (a, b) -> (calcRelativePri(a, currentTime) < calcRelativePri(b, currentTime) ? 1 : ((calcRelativePri(a, currentTime) == calcRelativePri(b, currentTime)) ? 0 : -1) ));
        activeGoals = activeGoals.slice(0, goaltableSize); // keep under AIKR
    }

    // event happened
    public function submitEvent(term:Term) {
        // scan all goals and decrement desire if it matches
        for(iGoal in activeGoals) {
            if (iGoal.condOps.ops.length == 0 && Par.checkSame(iGoal.condOps.cond, new Par([term]))) { // does term match?
                iGoal.beliefTv = new Tv(1.0, 0.998); // we have a belief for the goal when it happened
            }
        }
    }

    // helper to compute the relative priority of a goal
    private function calcRelativePri(activeGoal:ActiveGoal2, time:Int): Float {
        var timediff = time-activeGoal.creationTime;
        var decay = Math.exp(-decayrate*timediff);
        return decay*activeGoal.desire.exp(); // multiply by desire to not take care of undesired goals
    }
}

// helper to dump/debug all goals
class GoalSystemDebug {
    public static function debugAllGoals(goalSystem:GoalSystem):Array<String> {
        return goalSystem.activeGoals.map(v -> v.convToStr());
    }
}

class Dbg {
    // helper to debug
    public static function dbg(en:Bool, msg:String) {
        if(en) {
            // don't do this for javascript target!
            #if (js_es)
            #else
            Sys.println('[d] $msg');
            #end
        }
    }

}

// Q&A handler to handler answer to ^d question and to create a new goal with the unified variables
class DeclarativeAnswerHandler implements Nar.AnswerHandler2 {
    public var exec:Executive;
    public var goalSystem:GoalSystem;
    public var goal:ActiveGoal2; // goal for which the question was derived to handle the ^d pseudo-op

    public function new(exec:Executive, goal:ActiveGoal2, goalSystem:GoalSystem) {
        this.exec = exec;
        this.goal = goal;
        this.goalSystem = goalSystem;
    }
    
    public function report(sentence:Nar.Sentence, cycles:Int):Void {
        Dbg.dbg(true,'decl answer handler called for ^d');

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
            Dbg.dbg(true,'derived goal ${ExecUtils.convCondOpToStr(derivCondOp)}!');
        }

        // * create derived goal
        var derivedGoal:ActiveGoal2 = new ActiveGoal2(derivCondOp, goal.desire, goal.stamp, goalSystem.currentTime);

        // * register goal
        goalSystem.submitGoal2(exec, derivedGoal, EnumSentenceSource.DERIVED);
    }
}

// declarative pseudo-op
// ( <#y --> z>   &/ < ({SELF} * ($x, #y) --> x) --> ^d > ) =/> <$x --> goal>.

class ActiveGoal2 {
    public var condOps:CondOps;
    public var stamp:Stamp;
    public var creationTime:Int; // creation time in cycles

    public var qaWasQuestedAlready:Bool = false; // was a question already submitted to the declarative inference for ^d special op?

    public var desire:Tv = new Tv(1.0, 0.998); // how much do we want to realize the goal?

    public var beliefTv:Tv = null; // belief which has the same term

    public function new(condOps, desire, stamp, creationTime) {
        this.condOps = condOps;
        this.desire = desire;
        this.stamp = stamp;
        this.creationTime = creationTime;
    }

    /*Goal:
         If the expectation of its desire-value is e, and the system has a matching belief  with  expectation e′, h=|e−e′|.
         If there is no matching belief, h=|e−0.5|.
         It measures the extent the desired statement is already realized.
     */
    public function calcRealized():Float {
        var beliefExp:Float = beliefTv == null ? beliefTv.exp() : 0.5; // expectation of the belief
        return Math.abs(desire.exp() - beliefExp);
    }

    public function convToStr():String {
        var res = ExecUtils.convCondOpToStr(condOps) + "! ";
        res += desire.convToStr() + " ";
        res += 'desExp=${desire.exp()}';
        return res;
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

            res2.substr(0, res2.length-2-connector.length);
            return '( $res2 )';
        }

        var parEventsAsStr2 = concatTermStr(parEventsAsStr, "&|");

        if (condops.ops.length == 0) {
            return parEventsAsStr2;
        }
        else {
            var opsAsStr2 = concatTermStr(opsAsStr, "&/");
            return '($parEventsAsStr2 &/ $opsAsStr2)';
        }
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

    public var dtEffect:Int = 0; // time before effect happens
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

        var copStr = isConcurrentImpl ? "=|>" : "=/>";
        return '(${seq.join(" &/ ")} &/ +$dtEffect) $copStr ${effect.events.map(v -> TermUtils.convToStr(v))} {${calcFreq()} ${calcConf()}} // cnt=$evidenceCnt';
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

// enum for the source of a sentence
enum EnumSentenceSource {
    INPUT;
    DERIVED;
}
