/*
Copyright 2019 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

// run with
//    haxe --interp -main Sq2.hx

class Sq2 {
    public var mem:Memory = new Memory();

    // working set of tasks
    public var workingSet:WorkingSet = new WorkingSet();

    // working set of questions - which are importance sampled
    public var questionWorkingSet:ImportanceSampledWorkingSet = new ImportanceSampledWorkingSet();

    // used for debugging and unittesting
    // set to null to disable adding conclusions to this array
    public var conclusionStrArr:Array<String> = null;

    public var stampIdCounter = haxe.Int64.make(0, 0);

    public var globalCycleCounter = 0;

    public var taskIdCounter = 100000; // used to uniquly identify task globably

    public function new() {
    }

    // puts new input from the outside of the system into the system
    public function inputTerm(term:Term, tv:Tv, punctation:String) {
        var sentence = new Sentence(term, tv, new Stamp([stampIdCounter.copy()], new StructuralOriginsStamp([])), punctation);
        stampIdCounter = haxe.Int64.add(stampIdCounter, haxe.Int64.make(0,1));

        /* old code
        if (punctation == ".") { // only add to memory for judgments
            mem.updateConceptsForJudgement(sentence);
        }
        */

        var task:Task = null;

        if (punctation == ".") {
            task = new JudgementTask(sentence, taskIdCounter++);
        }
        else if (punctation == "?") {
            var q = new QuestionTask(sentence, QuestionLink.Null, taskIdCounter++);
            q.questionTime = globalCycleCounter;
            task = q;
        }
        else {
            throw "Invalid punctation!";
        }

        storeTasks([task], {putIntoWorkingSet:true});

        /* old code

        // add it to importance sampled set if it is a question
        if (punctation == "?") {
            var workingSetEntity:WorkingSetEntity = new WorkingSetEntity(task);
            workingSet.append(workingSetEntity);
        }
        else {
            workingQueueByDepth[0].tasks.push(task);
        } */
    }

    // puts new narsese input from the outside into the system
    public function input(narsese:String) {
        var parseResult = ProtoLexer.parse(narsese);

        var tv = null;
        if (parseResult.punctuation != "?") {
            tv = new Tv(1.0, 0.9); // standard TV
        }
        if (parseResult.tvFreq != null) {
            tv.freq = parseResult.tvFreq;
            tv.conf = parseResult.tvConf;
        }

        inputTerm(parseResult.term, tv, parseResult.punctuation);
    }

    private function reportAnswer(question:QuestionTask, sentence:Sentence) {
        var cycleStr = question.questionTime != -1 ? ('[${globalCycleCounter-question.questionTime}cycles]'): "";
        
        //var str = 'Answer:[  ?ms  ?cycl]${sentence.convToStr()}'; // report with time and cycles  // commented because we don't know the time it took
        var str = 'Answer:${cycleStr}${sentence.convToStr()}'; // report with time and cycles
        Sys.println(str);

        Sys.println('  from Q:${question.sentence.convToStr()}');


        if (conclusionStrArr != null) { // used for debugging and unittesting
            conclusionStrArr.push(str);
        }

        if (answerHandler != null) {
            answerHandler.report(sentence);
        }
    }

    // run the reasoner for a number of cycles
    public function process(cycles:Int = 20) {
        var cycleCounter = -1;
        while(true) { // main loop
            cycleCounter++;

            if (cycleCounter > cycles) {
                break;
            }

            globalCycleCounter++;

            if (Config.debug_derivations)   trace("");
            if (Config.debug_derivations)   trace("");
            if (Config.debug_derivations)   trace("");

            var primaryTask:Task = null;

            if (Math.random() < 0.3) {
                if (questionWorkingSet.entities.length == 0) {
                   continue;
                }

                var pickedMass:Float = Math.random()*questionWorkingSet.scoreSumOfUnboosted;
                var primaryTaskIdx = questionWorkingSet.calcIdxByScoreMass(pickedMass);
                primaryTask = questionWorkingSet.entities[primaryTaskIdx].task;
            }
            else {
                if (workingSet.entities.length == 0) {
                    continue; // nothing to work on, continue
                }

                //trace('utility:${workingSet.entities[0].calcUtility(0.0)}');

                primaryTask = workingSet.entities[0].task; // select best item
                workingSet.removeFirstItem();
            }
            
            var primarySentence = primaryTask.sentence;

            if (false) {
                Sys.println('');
                Sys.println('');
                Sys.println('sel task:${primarySentence.convToStr()}');
            }

            // Q&A
            if (primarySentence.punctation == "?") {
                var questionTask = cast(primaryTask, QuestionTask);

                // enumerate subterms
                // checked terms for enumeration of subterms of question
                var checkedTerms = TermUtils.enumTerms(primarySentence.term);

                for (iTermName in checkedTerms) {
                    // try to retrieve concept
                    if (!mem.hasConceptByName(TermUtils.convToStr(iTermName))) {
                        continue;
                    }
                    var nodeOfTerm: Node = mem.retConceptByName(TermUtils.convToStr(iTermName));

                    var needToRecompute = false;

                    // try to find better answer
                    for (iBelief in nodeOfTerm.judgments) {
                        //trace('Q&A check answer ${TermUtils.convToStr(iBelief.term)}');
                        //trace('unifies = ${Unifier.checkUnify(primarySentence.term, iBelief.term)}');

                        for(iBeliefTermView in TermUtils.rewriteSimToSimInhView(iBelief.term)) {
                            var iRewrittenBelief = new Sentence(iBeliefTermView, iBelief.tv, iBelief.stamp, iBelief.punctation);
                            iRewrittenBelief.derivationDepth = iBelief.derivationDepth;

                            var unifies:Bool = Unifier.checkUnify(primarySentence.term, iRewrittenBelief.term);

                            // check for same exp() because partial answers may have roughtly the same exp(), we still want to boost them
                            if (Math.abs(iRewrittenBelief.tv.exp() - questionTask.retBestAnswerExp()) < 0.001 && unifies) {
                                // we found an (potential) answer to a question
                                // now we can "boost" the answer (if it exists as a task, so we search the matching task and boost it)
                                for (iWorkingSetEntity in workingSet.entities) {
                                    if (iWorkingSetEntity.task.retPunctation() != ".") {
                                        continue;
                                    }
                                    
                                    var judgmentTask = cast(iWorkingSetEntity.task, JudgementTask);
                                    
                                    if (Sentence.equal(iWorkingSetEntity.task.sentence, iRewrittenBelief)) {
                                        judgmentTask.isAnswerToQuestion = true;
                                        needToRecompute = true;
    
                                        if(Config.debug_qaBoost)   trace('Q&A boost (potential) answer ${iWorkingSetEntity.task.sentence.convToStr()}');
    
                                        break;
                                    }
                                }
                            }
    
                            // check if we can propagate answer and propagate it down the question task chain/tree
                            // we can afford to do so because we assume that the depth of the tree is not to high
                            if (iRewrittenBelief.tv.exp() - questionTask.retBestAnswerExp() > -0.001 && unifies) {
                                // try to store candidate if it is not overlapping
                                /* commented because not useful {
                                    var noOverlap:Bool = [for (iCandidate in questionTask.bestAnswerSentenceCandidates) Stamp.checkOverlap(iCandidate.stamp, iBelief.stamp)].length == 0;
                                    if (noOverlap) {
                                        questionTask.bestAnswerSentenceCandidates.push(iRewrittenBelief);
    
                                        // limit size to keep under AIKR
                                        questionTask.bestAnswerSentenceCandidates = questionTask.bestAnswerSentenceCandidates.slice(0, 4);
                                        
                                        if (questionTask.bestAnswerSentenceCandidates.length > 1) {
                                            trace('${questionTask.bestAnswerSentenceCandidates[0].convToStr()}');
                                            trace('${questionTask.bestAnswerSentenceCandidates[1].convToStr()}');
                                            throw 'here';
                                        }
                                    }
                                } */
                                
                                propagatePartialAnswer(questionTask, iRewrittenBelief);
                            }
    
                            if (iRewrittenBelief.tv.exp() > questionTask.retBestAnswerExp() && unifies ) {
                                // found a better answer
                                questionTask.bestAnswerSentence = iRewrittenBelief;
                                reportAnswer(questionTask, iRewrittenBelief);
                            }
                        }
                    }

                    if (needToRecompute) {
                        //workingSet.recompute(); // recompute priority distribution
                    }
                }
            }

            var premiseTerm = primaryTask.sentence.term;
            var premiseTv = primaryTask.sentence.tv;
            var premisePunctation = primaryTask.sentence.punctation;
            var premiseStamp = primaryTask.sentence.stamp;
            var conclusionsSinglePremise:Array<Task> = deriveSinglePremise(primaryTask);

            var conclusionsTwoPremises = [];

            var conclusionTasks:Array<Task> = conclusionsSinglePremise;

            { // two premise derivation

                var timeBeforeTwoPremiseDeriv:Float = Sys.time();

                /* old code to select a random 2nd premise
                var selectedSecondaryPremiseTerm;
                { // select random subterm of premiseTerm
                    var subterms:Array<Term> = TermUtils.enumTerms(premiseTerm);
                    var idx = Std.random(subterms.length);
                    selectedSecondaryPremiseTerm = subterms[idx];
                }
                */

                // new code which iterates over all 2nd premises
                // is less fine-grained than selecting a random one but maybe it has less control problems
                for(selectedSecondaryPremiseTerm in TermUtils.enumTerms(premiseTerm)) {
                    
                    // select random secondary premise
                    var primaryConcept = mem.retConceptByName(TermUtils.convToStr(selectedSecondaryPremiseTerm));
                    if (primaryConcept != null && primaryConcept.judgments.length > 0) {
                        if (Config.debug_derivations)   trace("two premise derivation !");

                        for(secondarySentenceIdx in 0...primaryConcept.judgments.length) { // iterate over all for deterministic processing
                            var secondarySentence = primaryConcept.judgments[secondarySentenceIdx];
                            
                            var secondaryTerm = secondarySentence.term;
                            var secondaryTv = secondarySentence.tv;
                            var secondaryPunctation = secondarySentence.punctation;
                            var secondaryStamp = secondarySentence.stamp;
    
                            if (Config.debug_derivations)   trace("inf   " +  TermUtils.convToStr(premiseTerm) +     "   ++++    "+TermUtils.convToStr(secondaryTerm));
    
                            var conclDDepth: Int = Utils.min(primarySentence.derivationDepth, secondarySentence.derivationDepth) + 1;
    
                            if (!Stamp.checkOverlap(premiseStamp, secondaryStamp)) {
                                if (premisePunctation == "." && secondaryPunctation == "." && TermUtils.equal(premiseTerm, secondaryTerm)) { // can do revision
                                    var tv = Tv.revision(premiseTv, secondaryTv);
                                    var mergedStamp = Stamp.merge(premiseStamp, secondaryStamp);
                                    var revisedSentence = new Sentence(premiseTerm, tv, mergedStamp, ".");
                                    revisedSentence.derivationDepth = conclDDepth;
                                    primaryConcept.judgments[secondarySentenceIdx] = revisedSentence;
    
                                    { // print and add for debugging
                                        var conclusionAsStr = TermUtils.convToStr(premiseTerm) +  premisePunctation+" " + tv.convToStr();
                                        if (Config.debug_derivations)   trace(conclusionAsStr);
    
                                        if (conclusionStrArr != null) { // used for debugging and unittesting
                                            conclusionStrArr.push(conclusionAsStr);
                                        }
                                    }
                                }
                                else { // can't do revision, try normal inference
                                    var conclusionsTwoPremises2 = deriveTwoPremise(primaryTask.sentence, primaryTask, secondarySentence, null, conclDDepth,  conclusionTasks);
                                    conclusionsTwoPremises = conclusionsTwoPremises.concat(conclusionsTwoPremises2);
                                }
                            }
                            else {
                                if (Config.debug_derivations)   trace('   stampOverlap a=${premiseStamp.ids.map(v -> haxe.Int64.toStr(v))}  b=${secondaryStamp.ids.map(v -> haxe.Int64.toStr(v))}');
                            }
                        }
                    }
                }

                var timeAfterTwoPremiseDeriv:Float = Sys.time();
                if(false) trace('t two premise derivation=${timeAfterTwoPremiseDeriv-timeBeforeTwoPremiseDeriv}');
            }

            

            // adapter to create tasks for conclusions with two premises
            for (iConclusion in conclusionsTwoPremises) {
                var sentence = new Sentence(iConclusion.term, iConclusion.tv, iConclusion.stamp, iConclusion.punctation);
                sentence.derivationDepth = iConclusion.depth;

                var workingSetEntity = null;

                var task:Task = null;
                if (sentence.punctation == ".") {
                    task = new JudgementTask(sentence, taskIdCounter++);
                }
                else if (sentence.punctation == "?") {
                    task = new QuestionTask(sentence, QuestionLink.Null, taskIdCounter++);
                }
                else {
                    throw "Internal error";
                }

                conclusionTasks.push(task);
            }

            storeDerivations(conclusionTasks, {putIntoWorkingSet:true});
        }


        if (Config.debug_derivations) {
            debugSummary();
        }
    }

    // called when ever derivations were done which need to get stored
    public function storeDerivations(conclusionTasks:Array<Task>, flags:{putIntoWorkingSet:Bool}) {
        // filter out invalid statments like a-->a and a<->a
        // we are doing it here because these shouldn't get derived in the first place!
        conclusionTasks = conclusionTasks.filter(iConclusionTask -> {
            return switch (iConclusionTask.sentence.term) {
                case Cop(copula,a,b) if((copula == "-->" || copula == "<->" || copula == "==>" || copula == "<=>") && TermUtils.equal(a,b)):
                // trace('warning: derived nonsense ${iConclusionTask.sentence.convToStr()}');
                false;
                case _: true;
            };
        });

        if (Config.debug_derivations)   trace("|-");
        for (iConclusionTask in conclusionTasks) {
            var iConclusion = iConclusionTask.sentence;
            var conclusionAsStr = TermUtils.convToStr(iConclusion.term) +  iConclusion.punctation+(iConclusion.tv != null ? " " + iConclusion.tv.convToStr() : ""); // tv can be null
            if (Config.debug_derivations)   trace(conclusionAsStr);

            if (conclusionStrArr != null) { // used for debugging and unittesting
                conclusionStrArr.push(conclusionAsStr);
            }
        }



        if (Config.debug_derivations)   trace("");
        if (Config.debug_derivations)   trace("");
        if (Config.debug_derivations)   trace("");

        storeTasks(conclusionTasks, flags);
    }

    public function storeTasks(conclusionTasks:Array<Task>, flags:{putIntoWorkingSet:Bool}) {
        var tBefore:Float = Sys.time();

        if (Config.debug_derived) {
            for (iConclTask in conclusionTasks) {
                Sys.println('Derived:${iConclTask.sentence.convToStr()}    depth=${iConclTask.sentence.derivationDepth}');
            }
        }
        
        //if (flags.putIntoWorkingSet)
        {
            // store question-task lookup
            for (iConclusionTask in conclusionTasks.filter(it -> it.retPunctation() == "?")) {
                questionsByTaskId.set(iConclusionTask.id, cast(iConclusionTask, QuestionTask));
            }

            
            // put conclusions back into working set
            for (iConclusionTask in conclusionTasks) {
                var workingSetEntity = new WorkingSetEntity(iConclusionTask);
                
                if (iConclusionTask.retPunctation() == "?") {
                    // try to find conclusion in working set and add only if it doesn't yet exist
                    var existsSentenceInWorkingSet = false;
                    for (iWorkingSetEntity in questionWorkingSet.entities) {
                        if (Sentence.equal(iWorkingSetEntity.task.sentence, iConclusionTask.sentence)) {
                            existsSentenceInWorkingSet = true;
                            break;
                        }
                    }

                    if (!existsSentenceInWorkingSet) {
                        questionWorkingSet.append(workingSetEntity);
                    }
                }
                else {
                    var allow:Bool = true;
                    if (iConclusionTask.retPunctation() == ".") {
                        allow = iConclusionTask.sentence.tv.conf > 0.00000001; // allow only TV with conf above zero
                    }

                    if (allow) {
                        // try to find conclusion in working set and add only if it doesn't yet exist
                        // old code which was iterating
                        var timeBefore = Sys.time();
                        
                        /*
                        var existsSentenceInWorkingSet = false;
                        for (iWorkingSetEntity in workingSet.entities) {
                            if (Sentence.equal(iWorkingSetEntity.task.sentence, iConclusionTask.sentence)) {
                                existsSentenceInWorkingSet = true;
                                break;
                            }
                        }//*/
                        var existsSentenceInWorkingSet = workingSet.entitiesByTermExists(workingSetEntity);
                        
                        //trace('check time = ${Sys.time() - timeBefore}');

                        if (!existsSentenceInWorkingSet) {
                            workingSet.insert(workingSetEntity);
                        }
                    }

                }
            }
        }

        // store conclusion judgement
        for (iConclusionTask in conclusionTasks.filter(it -> it.retPunctation() == "." && it.sentence.tv.conf > 0.0000001)) {
            mem.updateConceptsForJudgement(iConclusionTask.sentence);
        }

        var tAfter:Float = Sys.time();
        if(true)  trace('t store=${tAfter-tBefore}');
    }

    public function debugSummary() {
        var numberOfConcepts = 0;
        {
            for (iConceptName in mem.conceptsByName.keys()) {
                numberOfConcepts++;
            }
        }

        Sys.println("Summary: ");
        Sys.println('   #concepts= $numberOfConcepts');
        Sys.println('   #workingset.entities= ${workingSet.entities.length}');
        Sys.println('   #questionWorkingset.entities= ${questionWorkingSet.entities.length}');
    }

    public function debugJudgements() {
        var allJudgements:Map<String, Bool> = new Map<String, Bool>();

        for (iConceptName in mem.conceptsByName.keys()) {
            var c = mem.conceptsByName.get(iConceptName);
            for (iJ in c.judgments) {
                allJudgements.set(iJ.convToStr(), true);
            }
        }

        for (iJudgementStr in allJudgements.keys()) {
            Sys.println(iJudgementStr);
        }
    }

    private var questionsByTaskId:Map<Int,QuestionTask> = new Map<Int,QuestionTask>();

    // tries to search and return a QuestionTask by the id of the task
    // /return value can be null if the referenced task is not anymore in memory (because of AIKR)
    private function retQuestionTaskById(taskId:Int): QuestionTask {
        if (!questionsByTaskId.exists(taskId)) {
            return null;
        }
        return questionsByTaskId.get(taskId);
    }

    // tries to search and return a Task by the id of the task
    // /return value can be null if the referenced task is not anymore in memory (because of AIKR)
    //private function retTaskById(taskId:Int): Task {
    //    // TODO< implement >
    //    trace('warning: retTaskById is not implemented!');
    //    return null;
    //}

    // Q&A - propagates a (partial) answer down the hierachy/tree of partial question tasks
    //
    // combines partial structural answers to more complete answers
    // ex: 
    // (a & b) --> c?
    //     a --> c?  answered with a --> c
    //     b --> c?  answered with b --> c
    // |- will compose answer to the question with partial answers:
    // (a & b) --> c
    //
    // calls itself recursivly!
    private function propagatePartialAnswer(questionTask:QuestionTask, answer:Sentence) {
        // helper function to propagate answer which answers the parent
        function propagatePossibleParentAnswer(conclusionTasks:Array<Task>, parentTask:QuestionTask){
            // only terms which unify with the question can be answers!
            for(iPotentialConclusionTask in conclusionTasks.filter(it -> it.retPunctation() == ".")) {
                var iPotentialConclusion = iPotentialConclusionTask.sentence;

                var unifies:Bool = Unifier.checkUnify(parentTask.sentence.term, iPotentialConclusion.term);
                if (unifies) {
                    if (Config.debug_derivations_qacomposition) { // debug potential conclusion
                        trace('|- ${TermUtils.convToStr(iPotentialConclusion.term)}');
                    }

                    // and we need to report the potential answer
                    // (with a recursive call, only when exp is above best reported one)

                    var sentence = new Sentence(iPotentialConclusion.term, iPotentialConclusion.tv, iPotentialConclusion.stamp, iPotentialConclusion.punctation);

                    if (iPotentialConclusion.tv.exp() > parentTask.retBestAnswerExp() && unifies ) {
                        // found a better answer
                        parentTask.bestAnswerSentence = sentence;
                        reportAnswer(parentTask, sentence);

                        // propagate
                        propagatePartialAnswer(parentTask, sentence);
                    }
                }
            }
        }


        switch(questionTask.questionLink) {
            case Null: // has no link - nothing to do!
            case StructuralSingle(parent): // has structural parent - we only need to derive structural transformations and try to answer the parent
            
            var parentTask:QuestionTask = retQuestionTaskById(parent);
            if (parentTask != null) { // can be null if no more in memory (AIKR)

                // task id is -1 because it is dummy
                var premiseTask = new JudgementTask(answer, -1);
                var conclusionTasks:Array<Task> = deriveSinglePremise(premiseTask);

                propagatePossibleParentAnswer(conclusionTasks, parentTask);
            }

            case ComposeSingle(index, parent): // has compositional parent - we need to try to compose partial answers and answer parent
            {
                var parentTask:QuestionTask = retQuestionTaskById(parent);
                if (parentTask != null) { // can be null if no more in memory (AIKR)

                    if (parentTask.questionCompositionChildrenLinks.length == 2) {
                        var linkedQuestionTasksByIndex:Array<QuestionTask> = [null, null];
                        
                        // enumerate linked question tasks - necessary because AIKR and because linked tasks can get forgotten
                        for(iLinkedTaskId in parentTask.questionCompositionChildrenLinks) {
                            var iLinkedTask:QuestionTask = retQuestionTaskById(iLinkedTaskId);
                            
                            if (iLinkedTask != null) { // can be null if it is not referenced anymore because of AIKR
                                switch(iLinkedTask.questionLink) {
                                    case ComposeSingle(index2, _):
                                    linkedQuestionTasksByIndex[index2] = iLinkedTask;
                                    case _: // ignore
                                }
                            }

                        }

                        // we have the linked question tasks for the composition
                        // now we have to make sure that they are valid
                        for(iLinkedTask in linkedQuestionTasksByIndex) {
                            if (iLinkedTask == null) {
                                return; // break propagation up because composition wasn't completely answered
                            }
                        }

                        // we are here when all questions are valid
                        // now we need to make sure that all partial questions were answered to compose the answer

                        for(iLinkedTask in linkedQuestionTasksByIndex) {
                            if (iLinkedTask.bestAnswerSentence == null) {
                                return; // composition wasn't completely answered!
                            }
                        }

                        //trace('debug structural compose');

                        // now we can combine the partial answers to (hopefully) get a composed answer

                        if (linkedQuestionTasksByIndex.length == 2) {
                            // check overlap

                            //trace('here, check stamp overlap');

                            //trace('${linkedQuestionTasksByIndex[0].bestAnswerSentence.convToStr()}');
                            //trace('${linkedQuestionTasksByIndex[1].bestAnswerSentence.convToStr()}');


                            if (Stamp.checkOverlap(linkedQuestionTasksByIndex[0].bestAnswerSentence.stamp, linkedQuestionTasksByIndex[1].bestAnswerSentence.stamp)) {
                                return;
                            }

                            if (Config.debug_derivations_qacomposition)   trace("inf : Q&A : try compose");
                            if (Config.debug_derivations_qacomposition) {
                                trace('   ${linkedQuestionTasksByIndex[0].bestAnswerSentence.convToStr()}');
                                trace('   ${linkedQuestionTasksByIndex[1].bestAnswerSentence.convToStr()}');
                            }

                            
                            var conclDDepth: Int = Utils.min(linkedQuestionTasksByIndex[0].bestAnswerSentence.derivationDepth, linkedQuestionTasksByIndex[1].bestAnswerSentence.derivationDepth) + 1;

                            var conclusionTasks:Array<Task> = [];
                            var potentialConclusions = deriveTwoPremise(
                                linkedQuestionTasksByIndex[0].bestAnswerSentence,
                                null,
                                linkedQuestionTasksByIndex[1].bestAnswerSentence,
                                null,

                                conclDDepth,
                                conclusionTasks
                            );

                            if (Config.debug_derivations_qacomposition) {
                                trace('|- (structural composition candidates)');
                            
                                for(iPotentialConclusion in potentialConclusions) {
                                    trace('   ${TermUtils.convToStr(iPotentialConclusion.term)}');
                                }
                            }

                            
                            // adapter to create tasks for conclusions with two premises
                            for (iConclusion in potentialConclusions) {
                                var sentence = new Sentence(iConclusion.term, iConclusion.tv, iConclusion.stamp, iConclusion.punctation);
                                sentence.derivationDepth = iConclusion.depth;

                                var workingSetEntity = null;
                                if (sentence.punctation == ".") {
                                    conclusionTasks.push(new JudgementTask(sentence, taskIdCounter++));
                                }
                                else if (sentence.punctation == "?") {
                                    conclusionTasks.push(new QuestionTask(sentence, QuestionLink.Null, taskIdCounter++));
                                }
                                else {
                                    throw "Internal error";
                                }
                            }

                            propagatePossibleParentAnswer(conclusionTasks, parentTask);
                        }
                        else {
                            trace('warning - structural composition of partial answers is not implemented for this case!');
                        }
                    }
                    else { // we don't support this yet!
                        trace('warning - structural composition for compositions of more than two elements is not supported: ${questionTask.sentence.convToStr()}');
                    }
                }
            }

            case HypotheticalRef2(parent):
            {
                var parentTask:QuestionTask = retQuestionTaskById(parent);
                if (parentTask != null) { // can be null if no more in memory (AIKR)
                    var ref2:Sentence = questionTask.ref2; // second premise
                    if (ref2 == null) {
                        throw "ref2 is null!";
                    }
                    else {
                        // * build all conclusions from answer and ref2
                        if (Stamp.checkOverlap(ref2.stamp, answer.stamp)) {
                            return;
                        }

                        if (Config.debug_derivations_qj)   trace("inf : Q&A : ?.");
                        if (Config.debug_derivations_qj) {
                            trace('   ${ref2.convToStr()}');
                            trace('   ${answer.convToStr()}');
                        }

                        
                        var conclDDepth: Int = Utils.min(ref2.derivationDepth, answer.derivationDepth) + 1;

                        
                        var conclusionTasks:Array<Task> = [];
                        var potentialConclusions = deriveTwoPremise(
                            ref2,
                            null,
                            answer,
                            null,

                            conclDDepth,
                            conclusionTasks
                        );

                        if (Config.debug_derivations_qj) {
                            trace('|- (QJ candidates)');
                        
                            for(iPotentialConclusion in potentialConclusions) {
                                trace('   ${TermUtils.convToStr(iPotentialConclusion.term)}');
                            }
                        }

                        
                        
                        // adapter to create tasks for conclusions with two premises
                        for (iConclusion in potentialConclusions) {
                            var sentence = new Sentence(iConclusion.term, iConclusion.tv, iConclusion.stamp, iConclusion.punctation);
                            sentence.derivationDepth = iConclusion.depth;

                            var workingSetEntity = null;
                            if (sentence.punctation == ".") {
                                conclusionTasks.push(new JudgementTask(sentence, taskIdCounter++));
                            }
                            else if (sentence.punctation == "?") {
                                conclusionTasks.push(new QuestionTask(sentence, QuestionLink.Null, taskIdCounter++));
                            }
                            else {
                                throw "Internal error";
                            }
                        }

                        // * feed conclusions into NAR
                        storeDerivations(conclusionTasks, {putIntoWorkingSet:false});
                        
                        // * try to answer parent question (and propagate if it answers)
                        propagatePossibleParentAnswer(conclusionTasks, parentTask);
                    }
                    
                }
            } // question was derived by creating a hypothesis for a possible answer  from a question and a judgement
        }
    }
    
    // /param conclDepth derivation depth of the conclusion
    public function deriveTwoPremise(premiseASentence:Sentence, premiseATask:Task, premiseBSentence:Sentence, premiseBTask:Task, conclDepth:Int,  conclTasks:Array<Task>) {
        var conclusionsTwoPremisesAB = deriveTwoPremiseInternal(premiseASentence, premiseATask, premiseBSentence, premiseBTask, conclDepth,  conclTasks);
        var conclusionsTwoPremisesBA = deriveTwoPremiseInternal(premiseBSentence, premiseBTask, premiseASentence, premiseATask, conclDepth,  conclTasks);
        return [].concat(conclusionsTwoPremisesAB).concat(conclusionsTwoPremisesBA);
    }


    // internal helper function which processes only one combination of premises (sides are not switched)
    // /param premiseATask can be null if premise is not associated with a task
    // /param premiseBTask can be null if premise is not associated with a task
    public function deriveTwoPremiseInternal(premiseASentence:Sentence, premiseATask:Task, premiseBSentence:Sentence, premiseBTask:Task, conclDepth:Int,  conclTasks:Array<Task>) {
        var premiseATerm:Term = premiseASentence.term;
        var premiseATv:Tv = premiseASentence.tv;
        var premiseAPunctation:String = premiseASentence.punctation;
        var premiseAStamp:Stamp = premiseASentence.stamp;

        var premiseBTerm:Term = premiseBSentence.term;
        var premiseBTv:Tv = premiseBSentence.tv;
        var premiseBPunctation:String = premiseBSentence.punctation;
        var premiseBStamp:Stamp = premiseBSentence.stamp;

        // checks if term is a set
        function checkSet(t:Term):Bool {
            return false; // TODO< implement >
        }
        
        // see Narjurue
        function checkNoCommonSubterm(a:Term, b:Term):Bool {
            return true; // TODO< implement >
        }

        var mergedStamp = Stamp.merge(premiseAStamp, premiseBStamp);

        var conclusions:Array<{term:Term, tv:Tv, punctation:String, stamp:Stamp, ruleName:String, depth:Int}> = [];

        // call to generated code for deriver
        Deriver.inferenceCode(premiseATerm, premiseAPunctation, premiseATv, premiseBTerm, premiseBPunctation, premiseBTv, mergedStamp, conclusions, conclDepth);


        // tries to unify a with b and return the unified term, returns null if it can't get unified
        // /param a contains variables
        // /param b contains values for the variables
        // /param varTypes
        function unifiesWithReplace(a, b, varTypes:String): Null<Term> {
            var unifiedMap = new Map<String, Term>();

            if (!Unifier.unify(a, b, unifiedMap)) {
                return null;
            }

            // apply variables and return substitution result
            return Unifier.substitute(a, unifiedMap, varTypes);
        }

        /* commented hypothetical question derivation because it doesn't add anything
        // "hypothetical" question derivation to guide backward inference
        // C --> (/ REL _ D)?
        // A --> (/ REL _ B).
        // |- (if unifies D B)
        // C <-> A?
        //
        // example:
        // ([filled] & rectangle) --> (/ leftOf _ {?1})?
        // {shape1}               --> (/ leftOf _ {shape2}).
        // |- ({?1} unifies with {shape2})
        // ([filled] & rectangle) <-> {shape1}?
        //    (question hints at possible solution path)

        // judgement will be linked as "ref2" variable for the use of the answer
        if (premiseAPunctation == "?" && premiseBPunctation == ".") {
            switch (premiseATerm) {
                case Cop("-->", c, Img(rel1, [ImgWild, d])):
                switch (premiseBTerm) {
                    case Cop("-->", a, Img(rel2, [ImgWild, b])) if (TermUtils.equal(rel1, rel2) && Unifier.checkUnify(d, b)):
                    {
                        var stamp = premiseAStamp; // TODO< add unique stampid to stamp >
                        var conclSentence = new Sentence(Cop("<->", c, a), null, stamp, "?");
                        
                        var link:QuestionLink = HypotheticalRef2(premiseATask.id);
                        var qTask:QuestionTask = new QuestionTask(conclSentence, link, taskIdCounter++);

                        trace('debug: ?. derived');
                        trace('debug:    ${premiseASentence.convToStr()}');
                        trace('debug:    |- ${conclSentence.convToStr()}');

                        if (premiseBSentence == null) {
                            trace('warning: ref2 is null!');
                        }
                        qTask.ref2 = premiseBSentence;

                        conclTasks.push(qTask);
                    }
                    case _: null;
                }
                case _: null;
            }
        }
        */


        // handling of implications for backward inference with detachment
        // ex:
        // <($0 * $1) --> c>?
        // (&&, <({0} * $0) --> x>, <({1} * $1) --> y>) ==> <($0 * $1) --> c>.
        // |-
        // (&&, <({0} * ?0) --> x>, <({1} * ?1) --> y>)?
        /* commented because not necessary for now
        if (premiseAPunctation == "?" && premiseBPunctation == ".") {
            switch(premiseBTerm) {
                case Cop("==>", implSubj, implPred) if (Unifier.checkUnify(premiseATerm, implPred)):
                    conclusions.push({term:implSubj, tv:null, punctation:"?", stamp:mergedStamp, ruleName:"NAL-6.two impl detachment"});
                
                case _: null;
            }
        }
        */

        if (premiseAPunctation == "." && premiseBPunctation == ".") {
            switch (premiseATerm) {
                case Cop("==>", Compound("&&", [compoundA0, compoundA1]), implPred):
                // TODO< var unification >
                // ex:
                // <(&&,<a --> x>,<c --> x>) ==> <X --> Y>>.
                // <a-->x>.
                // |-
                // <c --> x> ==> <X --> Y>.
                if (TermUtils.equal(compoundA0, premiseBTerm)) {
                    var conclusion = Term.Cop("==>", compoundA1, implPred);
                    conclusions.push({term: conclusion, tv:Tv.deduction(premiseATv, premiseBTv)/*TODO check*/, punctation:".", stamp:mergedStamp, ruleName:"NAL6-two impl ==> detach conj[0]", depth:conclDepth});
                }

                // TODO< var unification >
                // ex:
                // <(&&,<a --> x>,<c --> x>) ==> <X --> Y>>.
                // <c-->x>.
                // |-
                // <a --> x> ==> <X --> Y>.
                if (TermUtils.equal(compoundA1, premiseBTerm)) {
                    var conclusion = Term.Cop("==>", compoundA0, implPred);
                    conclusions.push({term: conclusion, tv:Tv.deduction(premiseATv, premiseBTv)/*TODO check*/, punctation:".", stamp:mergedStamp, ruleName:"NAL6-two impl ==> detach conj[1]", depth:conclDepth});
                }
                
                
                case _: null;
            }
        }


        if (premiseAPunctation == "." && premiseBPunctation == ".") {
            switch (premiseATerm) {
                // impl structural transformation with two premises ded
                case Cop(cop, subj, pred) if (cop == "<=>" || cop == "==>"):
                                
                //
                // ex:
                // <<$x-->d> <=> <$x-->e>>. [2]
                // <c-->d>. [1]
                // |-
                // <c-->e>. [1]
                //
                // ex:
                // <<$x-->d> ==> <$x-->e>>. [2]
                // <c-->d>. [1]
                // |-
                // <c-->e>. [1]
                var unifiedMap = new Map<String, Term>();
                if (Unifier.unify(subj, premiseBTerm, unifiedMap)) { // try to unify the subj of the impl or equiv w/ the other premise                    
                    var conclTerm = Unifier.substitute(pred, unifiedMap, "$");
                    conclusions.push({term: conclTerm, tv:Tv.deduction(premiseATv, premiseBTv)/*TODO check*/, punctation:".", stamp:premiseBStamp, ruleName:"NAL6-two impl structural transformation with two premises", depth:conclDepth});
                }

                case _: null;
            }
        }

        // NAL-6 impl/equiv backward inference
        if (premiseAPunctation == "." && premiseBPunctation == "?") {
            switch (premiseATerm) {
                case Cop(cop, subj, pred) if (cop == "<=>" || cop == "==>"):

                // TODO< write unittest for it >
                
                //
                // ex:
                // <<$x-->d> <=> <$x-->e>>.
                // <y-->e>?
                // |-
                // <x-->d>? [1]
                //
                // ex:
                // (OpenNARS does this one)
                // <<$x-->d> ==> <$x-->e>>.
                // <y-->e>?
                // |-
                // <x-->d>? [1]
                //
                var unifiedMap = new Map<String, Term>();
                if (Unifier.unify(pred, premiseBTerm, unifiedMap)) { // try to unify the subj of the impl or equiv w/ the other premise                    
                    var conclTerm = Unifier.substitute(subj, unifiedMap, "$");
                    conclusions.push({term: conclTerm, tv:null, punctation:"?", stamp:premiseBStamp, ruleName:"NAL6-two impl/equiv Q&A 1", depth:conclDepth});
                }

                case _: null;
            }
        }


        return conclusions;
    }

    // single premise derivation
    public function deriveSinglePremise(premiseTask:Task): Array<Task> {
        var premiseTerm = premiseTask.sentence.term;
        var premiseTermStructuralOrigins = premiseTask.sentence.stamp.structuralOrigins.arr;
        var premiseTv = premiseTask.sentence.tv;
        var premisePunctation = premiseTask.sentence.punctation;
        var premiseStamp = premiseTask.sentence.stamp;

        var conclusionTasks: Array<Task> = [];

        /* commented because conversion not necessary
        // NAL-2 conversion
        if (premisePunctation == ".") switch (premiseTerm) {
            case Cop(copula, subj, pred) if (copula == "-->"):

            var conclusionTerm = Term.Cop(copula, pred,subj);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );

                // ruleName:"NAL-2.single contraposition"
                var conclusionSentence = new Sentence(conclusionTerm, Tv.conversion(premiseTv), new Stamp(premiseStamp.ids, structuralOrigins), ".");
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                conclusionTasks.push(new JudgementTask(conclusionSentence, taskIdCounter++));
            }

            case _: null;
        }
         */

        // NAL-2 <-> / NAL-6 <=> structural transformation
        if (premisePunctation == ".") switch (premiseTerm) {
            case Cop(copula, subj, pred) if (copula == "<->" || copula == "<=>"):

            var conclusionTerm = Term.Cop(copula, pred,subj);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                
                // ruleName:(copula == "<->" ? "NAL-2" : "NAL-6") + ".single structural"
                var conclusionSentence = new Sentence(conclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), ".");
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                conclusionTasks.push(new JudgementTask(conclusionSentence, taskIdCounter++));
            }

            case _: null;
        }

        // NAL-2 / NAL-6 structural deduction
        // (S <-> P) |- (S --> P) Truth_StructuralDeduction
        // (S <=> P) |- (S ==> P) Truth_StructuralDeduction
        if (premisePunctation == ".") switch (premiseTerm) {
            case Cop(copula, subj, pred) if (copula == "<->" || copula == "<=>"):

            var conclusionTerm = Term.Cop(copula == "<->" ? "-->" : "==>", subj,pred);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                
                // ruleName:(copula == "<->" ? "NAL-2" : "NAL-6") + ".single structural ded"
                var conclusionSentence = new Sentence(conclusionTerm, Tv.structDeduction(premiseTv), new Stamp(premiseStamp.ids, structuralOrigins), ".");
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                conclusionTasks.push(new JudgementTask(conclusionSentence, taskIdCounter++));
            }

            case _: null;
        }

        // NAL-2 structural abduction
        // (S --> P) |- (S <-> P) Truth_StructuralAbduction
        if (premisePunctation == ".") switch (premiseTerm) {
            case Cop(copula, subj, pred) if (copula == "-->"):

            var conclusionTerm = Term.Cop("<->", subj,pred);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                
                //  ruleName:"NAL-2" + ".single structural abd"
                var conclusionSentence = new Sentence(conclusionTerm, Tv.structAbduction(premiseTv), new Stamp(premiseStamp.ids, structuralOrigins), ".");
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                conclusionTasks.push(new JudgementTask(conclusionSentence, taskIdCounter++));
            }

            case _: null;
        }

        // NAL-3 structural decomposition for question for better Q&A
        if (premisePunctation == "?") switch (premiseTerm) {
            // <(a & b) --> c>?
            // |-
            // <a --> c>?
            // <b --> c>?
            case Cop(cop, Compound(compType, compContent), pred) if (compType == "&" || compType == "|"):
            
            var premiseQuestionTask:QuestionTask = cast(premiseTask, QuestionTask);

            // were compositional questions ever derived?
            if (premiseQuestionTask.questionCompositionChildrenLinks.length != compContent.length) {
                premiseQuestionTask.questionCompositionChildrenLinks = []; // simplest solution is to flush 

                var componentIdx = 0; // used for linkage
                for(iCompContent in compContent) {

                    var conclusionTerm = Term.Cop(cop, iCompContent, pred);
    
                    // we don't need to check structural stamp, because it is not necessary
                    var structuralOrigins = new StructuralOriginsStamp([]);
    
                    // ruleName:"NAL-3" + '.single structural decompose $compType'
                    var conclusionSentence = new Sentence(conclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), premisePunctation);
                    conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                    if (premisePunctation == "?") {
                        var link:QuestionLink = QuestionLink.ComposeSingle(componentIdx, premiseQuestionTask.id); // we need to link them
                        var derivedQuestionTask = new QuestionTask(conclusionSentence, link, taskIdCounter++);
                        conclusionTasks.push(derivedQuestionTask);

                        // link from parent to children
                        premiseQuestionTask.questionCompositionChildrenLinks.push(derivedQuestionTask.id);
                    }
                    else {
                        trace('internal inconsistency!'); // path is not implemented/valid!
                    }
    
                    componentIdx++;
                }
            }

            case _: null;
        }


        // NAL-4  product to image transform
        if (premisePunctation == "." || premisePunctation == "?") switch (premiseTerm) {
            case Cop("-->", Prod([prod0, prod1]), inhPred):

            var conclusionTerm = Term.Cop("-->", prod0, Img(inhPred, [ImgWild, prod1]));
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                // <prod0 --> (/,inhPred,_,prod1)>
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                
                // ruleName:"NAL-6.single prod->img"
                var conclusionSentence = new Sentence(conclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), premisePunctation);
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                if (premisePunctation == "?") {
                    var link:QuestionLink = QuestionLink.StructuralSingle(premiseTask.id); // we need to link them
                    conclusionTasks.push(new QuestionTask(conclusionSentence, link, taskIdCounter++));
                }
                else {
                    conclusionTasks.push(new JudgementTask(conclusionSentence, taskIdCounter++));
                }
            }

            conclusionTerm = Term.Cop("-->", prod1, Img(inhPred, [prod0, ImgWild]));
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions

                // <prod1 --> (/,inhPred,prod0,_)>
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );

                // ruleName:"NAL-6.single prod->img"
                var conclusionSentence = new Sentence(conclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), premisePunctation);
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                if (premisePunctation == "?") {
                    var link:QuestionLink = QuestionLink.StructuralSingle(premiseTask.id); // we need to link them
                    conclusionTasks.push(new QuestionTask(conclusionSentence, link, taskIdCounter++));
                }
                else {
                    conclusionTasks.push(new JudgementTask(conclusionSentence, taskIdCounter++));
                }
            }

            case _: null;
        }

        // NAL-4  image to product transform
        if (premisePunctation == "." || premisePunctation == "?") switch (premiseTerm) {
            case Cop("-->", inhSubj, Img(inhPred, [ImgWild, prod1])):

            var conclusionTerm = Term.Cop("-->", Prod([inhSubj, prod1]), inhPred);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                // <(*, inhSubj, prod1) --> inhPred>
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                
                // ruleName:"NAL-6.single img->prod"
                var conclusionSentence = new Sentence(conclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), premisePunctation);
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                if (premisePunctation == "?") {
                    var link:QuestionLink = QuestionLink.StructuralSingle(premiseTask.id); // we need to link them
                    conclusionTasks.push(new QuestionTask(conclusionSentence, link, taskIdCounter++));
                }
                else {
                    conclusionTasks.push(new JudgementTask(conclusionSentence, taskIdCounter++));
                }
            }


            case Cop("-->", inhSubj, Img(inhPred, [prod0, ImgWild])):

            var conclusionTerm = Term.Cop("-->", Prod([prod0, inhSubj]), inhPred);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                // <(*, prod0, inhSubj) --> inhPred>
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );

                // ruleName:"NAL-6.single img->prod"
                var conclusionSentence = new Sentence(conclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), premisePunctation);
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                if (premisePunctation == "?") {
                    var link:QuestionLink = QuestionLink.StructuralSingle(premiseTask.id); // we need to link them
                    conclusionTasks.push(new QuestionTask(conclusionSentence, link, taskIdCounter++));
                }
                else {
                    conclusionTasks.push(new JudgementTask(conclusionSentence, taskIdCounter++));
                }
            }

            case _: null;
        }

        // NAL-4 structural decomposition
        //<(*,a,b) --> (*,c,d)>.
        //|-
        //<a-->c>.
        // (and other forms)
        //
        //<(*,a,b) <-> (*,c,d)>.
        //|-
        //<a<->c>.
        // (and other forms)
        if (premisePunctation == ".") switch (premiseTerm) {
            case Cop(cop, Prod([subj0, subj1]),Prod([pred0, pred1])) if (cop == "-->" || cop == "<->"):

            var conclusionTerms = [Term.Cop(cop, subj0, pred0), Term.Cop(cop, subj1, pred1)];
            
            for (iConclusionTerm in conclusionTerms) {
                if (!Utils.contains(premiseTermStructuralOrigins, iConclusionTerm)) { // avoid deriving the same structural conclusions
                    var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                    
                    // ruleName:"NAL-6.single struct decomposition"
                    var conclusionSentence = new Sentence(iConclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), premisePunctation);
                    conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                    conclusionTasks.push(new JudgementTask(conclusionSentence, taskIdCounter++));
                }
            }

            case _: null;
        }


        if (Config.debug_derivations)   trace(TermUtils.convToStr(premiseTerm)+premisePunctation);

        return conclusionTasks;
        
    }

    public var answerHandler:AnswerHandler = null; // answer handler which is invoked when ever a new answer is derived
}

class Node {
    public var name:Term; // name of the concept

    public var judgments: Array<Sentence> = []; // all judgments of the concept

    public function new(name) {
        this.name = name;
    }
}

// handler which is called when ever a new answer is derived
interface AnswerHandler {
    function report(sentence:Sentence):Void;
}

class Memory {
    // name key is name as string
    public var conceptsByName:Map<String, Node> = new Map<String, Node>();

    public function new() {}

    public function hasConceptByName(name:String) {
        return conceptsByName.get(name) != null;
    }

    public function retConceptByName(name:String): Node {
        return conceptsByName.get(name);
    }

    public function addConcept(concept:Node) {
        conceptsByName.set( TermUtils.convToStr(concept.name) , concept);
    }

    // puts judgement into corresponding concepts
    public function updateConceptsForJudgement(sentence:Sentence) {
        for (iTermName in TermUtils.enumTerms(sentence.term)) {
            var nodeOfTerm;
            
            // retrieve or create concept
            if (hasConceptByName(TermUtils.convToStr(iTermName))) {
                nodeOfTerm = retConceptByName(TermUtils.convToStr(iTermName));
            }
            else {
                nodeOfTerm = new Node(iTermName);
                addConcept(nodeOfTerm);
            }

            // we need to check for the existence of a judgment with the same stamp and TV
            var exists = false;
            for (iJudgment in nodeOfTerm.judgments) {
                if (Sentence.equal(iJudgment, sentence)) {
                    exists = true;
                    break;
                }
            }

            if (exists) {
                continue;
            }

            // update
            nodeOfTerm.judgments.push(sentence);

            // sort judgments by metric and limit size
            nodeOfTerm.judgments.sort( (a, b) -> (a.tv.exp() < b.tv.exp() ? 1 : ((a.tv.exp() == b.tv.exp()) ? 0 : -1) ));
            nodeOfTerm.judgments = nodeOfTerm.judgments.slice(0, Config.beliefsPerNode);
        }
    }
}



class Sentence {
    public var term:Term;
    public var tv:Tv;
    public var stamp:Stamp;

    public var punctation:String;

    public var derivationDepth:Int = 0;

    public function new(term, tv, stamp, punctation) {
        this.term = term;
        this.tv = tv;
        this.stamp = stamp;
        this.punctation = punctation;
    }

    public function convToStr():String {
        var res = TermUtils.convToStr(term) +  punctation+" ";
        if (tv != null) { // can be null
            res += tv.convToStr();
        }
        return res;
    }

    public static function equal(a:Sentence, b:Sentence):Bool {
        var epsilon = 0.00001;
        var isTruthEqual = false;
        if (a.tv == null && b.tv == null) {
            isTruthEqual = true;
        }
        else if (a.tv != null && b.tv != null) {
            isTruthEqual = Math.abs(a.tv.freq-b.tv.freq) < epsilon && Math.abs(a.tv.conf-b.tv.conf) < epsilon;
        }

        var isTermEqual = TermUtils.equal(a.term, b.term);
        return isTruthEqual && isTermEqual && a.punctation == b.punctation && Stamp.checkOverlap(a.stamp, b.stamp);
    }
}

// abstract class for a task
class Task {
    public var sentence:Sentence;

    public var id:Int; // unique id of the task

    public function new(sentence, id) {
        this.sentence = sentence;
        this.id = id;
    }

    public function retPunctation():String {
        return sentence.punctation;
    }
}

class QuestionTask extends Task {
    // TODO< link it with a weak link by a global id because AIKR >
    public var questionLink:QuestionLink; // links the question to a parent question
    public var questionCompositionChildrenLinks:Array<Int> = []; // links to compositional children (for one single composition), task id's are referenced

    public var bestAnswerSentence:Sentence = null;

    public var questionTime:Int = -1; // global cycle time of the question, -1 if it is not tracked

    public var ref2:Sentence = null; // reference to 2nd premise of this question - used for hypothetical question derivation to guide search process

    public function new(sentence, questionLink, id) {
        super(sentence, id);
        this.questionLink = questionLink;
    }

    public function retBestAnswerExp(): Float {
        if (bestAnswerSentence == null) {
            return 0.0;
        }
        return bestAnswerSentence.tv.exp();
    }
}

// parent are id of tasks
enum QuestionLink {
    Null; // isn't linked
    StructuralSingle(parent:Int); // question was derived by structural derivation with single premise
    ComposeSingle(index:Int, parent:Int); // question was derived by structural decomposition of compound, ex: (a & b)? |- a? |- b?
                                                   // index is the index in the composition
    HypotheticalRef2(parent:Int); // question was derived by creating a hypothesis for a possible answer  from a question and a judgement
}

class JudgementTask extends Task {
    public var isAnswerToQuestion:Bool = false; // is it a answer to a question?    

    public function new(sentence, id) {
        super(sentence, id);
    }
}




class WorkingSetEntity {
    public var task:Task;

    public var accuScore = 0.0; // accumulated score of the items in working set up to this item, we store it here for efficiency

    public function new(task) {
        this.task = task;
    }

    // /param scoreSumOfUnboosted
    public function calcUtility(scoreSumOfUnboosted:Float) {
        if (task.retPunctation() == "?") {
            // TODO< take time into account >
            // questions don't have a TV so we have to provide a specific base utility
            return 0.8; // TODO< expose as tunable parameter >
        }

        // TODO< take time into account >
        var utility:Float = 0.0;
        if (task.retPunctation() == "." && cast(task, JudgementTask).isAnswerToQuestion) {
            utility = /* commented because something else doesn't work yet   sentence.tv.conf * */ 2.0 * scoreSumOfUnboosted; // "boost" answer to question
        }
        else {
            utility = task.sentence.tv.conf;
        }

        // more deeper sentences get less attention
        utility = utility * Math.pow(0.8, task.sentence.derivationDepth);

        // TODO< reduce utility by complexity
        //var complexity:Int = TermUtils.calcComplexity(task.sentence.term);
        //utility *= Math.pow(complexity, -1.6);

        { // HACK to reduce utility by appearance of Q&A terms
            /* disabled because it is hardcoded for Shapeworld
            var termAsStr:String = TermUtils.convToStr(task.sentence.term);
            var foundA:Bool = termAsStr.indexOf("leftOf")!=-1;
            var foundB:Bool = termAsStr.indexOf("filled")!=-1;
            var foundC:Bool = termAsStr.indexOf("rectangle")!=-1;

            var foundScore:Float = (foundA?1:0) + (foundB?1:0) + (foundC?1:0);
            foundScore *= (1.0 / 3); // normalize
            foundScore = Math.max(0.1, foundScore);

            utility *= foundScore;
            */
        }

        return utility;
    }
}


class BaseWorkingSet {
    public var entities:Array<WorkingSetEntity> = [];

    public var scoreSumOfUnboosted:Float = 0.0; // sum of all scores of unboosted entities

    // used to quickly look up if task exist by sentence
    private var entitiesByTerm:Map<String, Array<WorkingSetEntity>> = new Map<String, Array<WorkingSetEntity>>();

    public function entitiesByTermExists(e:WorkingSetEntity):Bool {
        var key:String = TermUtils.convToStr(e.task.sentence.term);
        if (!entitiesByTerm.exists(key)) {
            return false; // doesn't know key -> sentence doesn't exist
        }

        var candidates:Array<WorkingSetEntity> = entitiesByTerm.get(key);
        for(iCandidate in candidates) {
            if (Sentence.equal(iCandidate.task.sentence, e.task.sentence)) {
                return true;
            }
        }
        return false;
    }

    private function entitiesByTermInsertIfNotExistBySentence(e:WorkingSetEntity) {
        if (entitiesByTermExists(e)) {
            return; // exist already, skip
        }

        var key:String = TermUtils.convToStr(e.task.sentence.term);
        var candidates:Array<WorkingSetEntity> = null;
        if (entitiesByTerm.exists(key)) {
            candidates = entitiesByTerm.get(key);
        }
        else {
            candidates = [];
        }
        candidates.push(e);
        entitiesByTerm.set(key, candidates);
    }


    public function new() {}

    public function debug(): String {
        var labelBoosted = true; // do we label boosted entries?

        var res = "";

        for(iEntity in entities) {
            //if(iEntity.isAnswerToQuestion)
            res += '   ${iEntity.task.sentence.convToStr()}:  ${labelBoosted && (iEntity.task.retPunctation() == "." && cast(iEntity.task, JudgementTask).isAnswerToQuestion) ? "BOOSTED" : ""}  score=${iEntity.calcUtility(scoreSumOfUnboosted)} accScore=${iEntity.accuScore}\n';
        }
        
        res += 'ws count=${entities.length}\n';

        return res;
    }
}

// working set which is (totally) ordered by some utility
// IMPL DETAIL< is using a hash-lookup to accelerate lookup by sentence >
class WorkingSet extends BaseWorkingSet {
    public function new() {
        super();
    }

    // insert sorted by total score
    public function insert(entity:WorkingSetEntity) {
        entitiesByTermInsertIfNotExistBySentence(entity);

        // TODO< do real insertition with binary search/insert! >

        var timeBefore = Sys.time();

        entities.push(entity);
        entities.sort((a, b) -> {
            if (Math.abs(a.calcUtility(scoreSumOfUnboosted) - b.calcUtility(scoreSumOfUnboosted)) < 0.0000001) {
                // ASSUMPTION< higher id is older task >
                if (a.task.id == b.task.id) {
                    return 0;
                }
                if (a.task.id > b.task.id) {
                    return 1;
                }
                return -1;
            }

            return (a.calcUtility(scoreSumOfUnboosted) < b.calcUtility(scoreSumOfUnboosted) ? 1 : -1);
        });

        entities = entities.slice(0, Config.mem_TasksMax); // keep under AIKR
        
        var time = Sys.time() - timeBefore;
        if(true) trace('insert t=${time}');
    }

    // called when first item has to get removed
    public function removeFirstItem() {
        var firstItem:WorkingSetEntity = entities[0];
        entities = entities.slice(1);

        // remove it from the hash
        var key:String = TermUtils.convToStr(firstItem.task.sentence.term);
        if (!entitiesByTerm.exists(key)) {
            // TODO< figure out why this bug happens! >
            // trace('w key doesn\'t exist but should: ${key}');
        }
        if (entitiesByTerm.exists(key)) { // check to make sure, shouldn't fail
            var candidates:Array<WorkingSetEntity> = entitiesByTerm.get(key);
            { // remove candidate
                var idx:Int = 0;
                var found=false;
                while(idx < candidates.length) {
                    if (Sentence.equal(candidates[idx].task.sentence, firstItem.task.sentence)) {
                        found = true;
                        break;
                    }
                    idx++;
                }

                if (found) { // not defined if not found
                    candidates = ArrUtils.removeAt(candidates, idx);
                }
            }

            entitiesByTerm.set(key, candidates);

        }
    }
}

// working set which is sampled with importance sampling
class ImportanceSampledWorkingSet extends BaseWorkingSet {
    public function new() {
        super();
    }

    // append, maintains invariants
    public function append(entity:WorkingSetEntity) {
        entities.push(entity);

        if (entities.length >= 2) {
            entities[entities.length-1].accuScore = entities[entities.length-2].accuScore;
        }

        if (!(entity.task.retPunctation() == "." && cast(entity.task, JudgementTask).isAnswerToQuestion)) {
            scoreSumOfUnboosted += entity.calcUtility(0.0);
        }

        entities[entities.length-1].accuScore += entity.calcUtility(scoreSumOfUnboosted);
    }

    // forces a recomputation of the entire distribution
    public function recompute() {
        if (entities.length == 0) {
            return;
        }

        // recompute sum of unboosted entities
        scoreSumOfUnboosted = 0.0;
        for(iEntity in entities) {
            if (!(iEntity.task.retPunctation() == "." && cast(iEntity.task, JudgementTask).isAnswerToQuestion)) {
                scoreSumOfUnboosted += iEntity.calcUtility(0.0);
            }
        }

        entities[0].accuScore = entities[0].calcUtility(scoreSumOfUnboosted);

        for(idx in 1...entities.length) {
            entities[idx].accuScore = entities[idx-1].accuScore + entities[idx].calcUtility(scoreSumOfUnboosted);
        }
    }

    // computes the index of the entity by chosen "score mass"
    // necessary for fair probabilistic selection of tasks
    public function calcIdxByScoreMass(mass:Float, depth=0, minIdx=0, maxIdx=null): Int {
        if (maxIdx == null) {
            maxIdx = entities.length-1;
        }

        var accuScoreAtMin = entities[minIdx].accuScore;
        var accuScoreAtMax = entities[maxIdx].accuScore;


        //if (depth > 5) {
        //    throw "DEBUG ERROR";
        //}
        //
        //trace('l=${entities.length}');
        //trace('calcIdxByScoreMass() minIdx=$minIdx maxIdx=$maxIdx');

        if (minIdx == maxIdx - 1) {
            //trace("BEFORE");

            //for (iEntity in entities) {
            //    trace('   ${TermUtils.convToStr(iEntity.sentence.term)}${iEntity.sentence.punctation}  score=${iEntity.calcUtility()}');
            //}

            if (mass < accuScoreAtMin) {
                return minIdx;
            }
            return maxIdx;
        }
        if (minIdx == maxIdx) {
            return minIdx;
        }


        // we use binary search

        var midIdx = Std.int((maxIdx+minIdx) / 2);
        var accuScoreAtMid = entities[midIdx].accuScore;

        if (mass < accuScoreAtMid) {
            return calcIdxByScoreMass(mass, depth+1, minIdx, midIdx);
        }
        else {
            return calcIdxByScoreMass(mass, depth+1, midIdx, maxIdx);
        }
    }
}

class ArrUtils {
    @:generic public static function removeAt<T>(arr:Array<T>, idx:Int):Array<T> {
        var before = arr.slice(0, idx);
        var after = arr.slice(idx+1, arr.length);
        return before.concat(after);
    }

    public static function main() {
        trace(removeAt([0], 0));
        trace("---");
        trace(removeAt([0, 1], 0));
        trace(removeAt([0, 1], 1));
        trace("---");
        trace(removeAt([0, 1, 2], 0));
        trace(removeAt([0, 1, 2], 1));
        trace(removeAt([0, 1, 2], 2));
    }
}

class WorkingArr {
    public var tasks:Array<Task> = [];

    public function new() {}
}


class Config {
    public static var mem_TasksMax = 5000; // maximal number of tasks in winner takes all

    public static var beliefsPerNode:Int = 30;
    public static var debug_derived:Bool = false; // debug derivations
    public static var debug_derivations:Bool = false; // debug derivation process to console
    public static var debug_derivations_qacomposition:Bool = false; // debug composition for Q&A to console?
    public static var debug_derivations_qj:Bool = true; // debug question-judgement processes?
    
    public static var debug_qaBoost:Bool = false; // debug boosted answers for questions to console?
}


class Unifier {
    // substitute variables with actual variables
    // /param varTypes types of variables, can be any string of the combination "?","#","$"
    public static function substitute(term:Term, unifiedMap:Map<String, Term>, varTypes:String): Term {
        function substituteArr(arr:Array<Term>):Array<Term> {
            return arr.map(term -> substitute(term, unifiedMap, varTypes));
        }
        
        switch (term) {
            case Name(_): return term;
            case Compound(type, content): return Compound(type, substituteArr(content));
            case Cop(copula, subj, pred): return Cop(copula, substitute(subj, unifiedMap, varTypes), substitute(pred, unifiedMap, varTypes));
            case Prod(content):
            return Prod(substituteArr(content));
            case Img(base, content):
            var substBase = substitute(base, unifiedMap, varTypes);
            var substContent = substituteArr(content);
            return Img(substBase, substContent); 
            case ImgWild: return ImgWild;
            case Var(type,name): 
            if (varTypes.indexOf(type)!=-1) {
                var varValue = unifiedMap.get('$type$name');
                if (varValue == null) {
                    return term; // return untouched because we couldn't find it
                }
                else {
                    return varValue; // return substituted
                }
            }
            else {
                return term; // return untouched term because we can't substitute it anyways
            }

            case Str(_): return term;

            case Set(type,content):
            // substitute vars in set
            return Set(type,substituteArr(content));
        }
    }

    // checks if the two terms unify
    public static function checkUnify(a:Term, b:Term) {
        return unify(a, b, new Map<String, Term>());
    }


    // /param unifiedMap map my variable names and their assignments
    // /return can it be unified?
    public static function unify(a:Term, b:Term, unifiedMap:Map<String, Term>): Bool {
        if (TermUtils.isVar(a) && !TermUtils.isVar(b)) {
            return unifyVarWithNonVar(a, b, unifiedMap);
        }
        else if (!TermUtils.isVar(a) && TermUtils.isVar(b)) {
            return unifyVarWithNonVar(b, a, unifiedMap);
        }
        else if (TermUtils.isVar(a) && TermUtils.isVar(b)) {
            return false; // can't unify variable with variable!
        }
        // else we handle all other cases here
        
        if (TermUtils.equal(a, b) && !containsVar(a) && !containsVar(b)) {
            return true;
        }

        // a or b are not variables and are not equal

        // unifies array
        function unifyArr(aArr:Array<Term>, bArr:Array<Term>): Bool {
            if (aArr.length != bArr.length) {
                return false;
            }
            for (idx in 0...aArr.length) {
                if (!unify(aArr[idx],bArr[idx],unifiedMap)) {
                    return false;
                }
            }
            return true;
        } 

        switch (a) {
            case Name(_):
            return false; // doesn't unify because not equal
            case Compound(typeA, contentA):
            switch (b) {
                case Compound(typeB, contentB) if (typeA==typeB):
                return unifyArr(contentA, contentB);
                case _:
                return false; // can't unify because it is different
            }
            case Cop(copulaA, subjA, predA):
            switch (b) {
                case Cop(copulaB, subjB, predB) if (copulaA == copulaB):
                return unify(subjA, subjB, unifiedMap) && unify(predA, predB, unifiedMap);
                case _:
                return false; // can't unify because it is different
            }
            case Prod(contentA):
            switch (b) {
                case Prod(contentB):
                return unifyArr(contentA, contentB);
                case _:
                return false; // can't unify because it is different
            }
            case Img(baseA, contentA):
            switch (b) {
                case Img(baseB, contentB):
                if (!unify(baseA, baseB, unifiedMap) ) {
                    return false;
                }
                return unifyArr(contentA, contentB);
                case _:
                return false; // can't unify because it is different
            }
            case ImgWild:
            return false; // doesn't unify because not equal
            case Var(typeA,nameA):
            throw "Internal error - should be handled earilier in function!";
            case Str(_):
            return false; // doesn't unify because not equal
            case Set(typeA,contentA):
            switch (b) {
                case Set(typeB, contentB) if (typeA==typeB):
                return unifyArr(contentA, contentB);
                case _:
                return false; // can't unify because it is different
            }
        }

        return true; // can unify
    }

    // tries to unify a variable with a non-variable
    // /return null if it can't get unified, otherwise the unified term
    private static function unifyVarWithNonVar(varTerm:Term, nonvarTerm:Term, unifiedMap:Map<String, Term>): Bool {
        var varType;
        var varName;
        switch (varTerm) {
            case Var(varType2,varName2):
            varType = varType2;
            varName = varName2;
            case _: throw "Internal Error - varTerm must be a variable!";
        }

        var fusedVarTypeName = '$varType$varName';

        // lookup
        var lookupResultTerm:Term = unifiedMap.get(fusedVarTypeName);
        if( lookupResultTerm != null ) { // if variable has already a assigment
            return TermUtils.equal(lookupResultTerm, nonvarTerm); // lookuped term must be the same term, else it doesn't unify!
        }

        // assign term to variable
        unifiedMap.set(fusedVarTypeName, nonvarTerm);

        return true;
    }

    private static function containsVar(a:Term): Bool {
        // TODO TODO TODO
        return false;
    }
}




class Assert {
    public static function assert(v:Bool, msg:String) {
        if(!v) {
            Sys.println(msg);
        }
    }
}



enum EnumArcType {
    TOKEN;
    OPERATION;  // TODO< is actualy symbol? >
    ARC;        // another arc, info is the index of the start
    KEYWORD;    // Info is the id of the Keyword

    END;        // Arc end
    NIL;        // Nil Arc

    ERROR;      // not used Arc
}

@generic
class Arc<EnumOperationType> {
    public var type: EnumArcType;
    public var callback: (parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) -> Void;
    public var next: Int;
    public var alternative: Null<Int>;

    public var info: Int; // Token Type, Operation Type and so on

    public function new(type, info, callback, next, alternative) {
        this.type        = type;
        this.info        = info;
        this.callback    = callback;
        this.next        = next;
        this.alternative = alternative;
    }
}

enum EnumRecursionReturn {
    ERROR; // if some error happened, will be found in ErrorMessage
    OK;
    BACKTRACK; // if backtracking should be used from the caller
}


@generic
class Parser<EnumOperationType> {
    public function new() {
        //this.Lines ~= new Line!EnumOperationType();
    }

    /*abstract*/ public function convOperationToCode(op: EnumOperationType): Int {
        throw "Abstract method called!"; // must be implemented by class
    }

    /** \brief 
     *
     * \param arcTableIndex is the index in the ArcTable
     * \return
     */
    // NOTE< this is written recursive because it is better understandable that way and i was too lazy to reformulate it >
    private function parseRecursive(arcTableIndex:Int): EnumRecursionReturn {
        var ateAnyToken = false;
        var returnValue = EnumRecursionReturn.BACKTRACK;

        while(true) {
            if(ParserConfig.debugParser) trace("ArcTableIndex " + arcTableIndex);

            switch( this.arcs[arcTableIndex].type ) {
                ///// NIL
                case NIL:
                // if the alternative is null we just go to next, if it is not null we follow the alternative
                // we do this to simplify later rewriting of the rule(s)
                if( this.arcs[arcTableIndex].alternative == null ) {
                    returnValue = EnumRecursionReturn.OK;
                }
                else {
                    returnValue = EnumRecursionReturn.BACKTRACK;
                }

                ///// OPERATION
                case OPERATION:
                if( this.currentToken.type == EnumTokenType.OPERATION && this.arcs[arcTableIndex].info == convOperationToCode(this.currentToken.contentOperation) ) {
                    returnValue = EnumRecursionReturn.OK;
                }
                else {
                    returnValue = EnumRecursionReturn.BACKTRACK;
                }

                ///// TOKEN
                case TOKEN:
                function convTokenTypeToInfoNumber(type) {
                    return switch (type) {
                        case EnumTokenType.NUMBER: 0;
                        case EnumTokenType.IDENTIFIER: 1;
                        case EnumTokenType.KEYWORD: 2;
                        case EnumTokenType.OPERATION: 3;
                        case EnumTokenType.ERROR: 4; //
                        case EnumTokenType.STRING: 5;
                        case EnumTokenType.EOF: 6;
                    }
                }

                if( this.arcs[arcTableIndex].info == convTokenTypeToInfoNumber(this.currentToken.type) ) {
                    returnValue = EnumRecursionReturn.OK;
                }
                else {
                    returnValue = EnumRecursionReturn.BACKTRACK;
                }


                ///// ARC
                case ARC:
                returnValue = this.parseRecursive(this.arcs[arcTableIndex].info);
                
                ///// END
                case END:

                // TODO< check if we really are at the end of all tokens >

                if(ParserConfig.debugParser) trace("end");

                return EnumRecursionReturn.OK;

                case ERROR:
                throw "parsing error!";

                case KEYWORD:
                // TODO< implement >
                throw "Internal error!";
            }



         if( returnValue == EnumRecursionReturn.ERROR ) {
            return EnumRecursionReturn.ERROR;
         }

         if( returnValue == EnumRecursionReturn.OK ) {
            if (this.arcs[arcTableIndex].callback != null) {
                this.arcs[arcTableIndex].callback(this, this.currentToken);
            }
            returnValue = EnumRecursionReturn.OK;
         }

         if( returnValue == EnumRecursionReturn.BACKTRACK ) {
            // we try alternative arcs
            if(ParserConfig.debugParser) trace("backtracking");

            if( this.arcs[arcTableIndex].alternative != null ) {
               arcTableIndex = this.arcs[arcTableIndex].alternative;
            }
            else if( ateAnyToken ) {
               return EnumRecursionReturn.ERROR;
            }
            else {
               return EnumRecursionReturn.BACKTRACK;
            }
         }
         else {
            // accept formaly the token

            if(
               this.arcs[arcTableIndex].type == EnumArcType.OPERATION ||
               this.arcs[arcTableIndex].type == EnumArcType.TOKEN
            ) {

               if(ParserConfig.debugParser) trace("eat token");

               var calleeSuccess = this.eatToken();

               if( !calleeSuccess ) {
                  throw "Internal Error!\n";
               }

               ateAnyToken = true;
            }

            arcTableIndex = this.arcs[arcTableIndex].next;
         }
      }
   }

   /** \brief do the parsing
    *
    * \param ErrorMessage is the string that will contain the error message when an error happened
    * \return true on success
    */
    public function parse(): Bool {
        this.currentToken = null;

        //this.setupBeforeParsing();
        lines = [new Line<EnumOperationType>()]; // reset the lines

        // read first token
        var calleeSuccess = this.eatToken();
        if( !calleeSuccess ) {
            throw "Internal Error!";
        }

        if(ParserConfig.debugParser) this.currentToken.debugIt();

        var recursionReturn = this.parseRecursive(1);

        if( recursionReturn == EnumRecursionReturn.ERROR ) {
            return false;
        }
        else if( recursionReturn == EnumRecursionReturn.BACKTRACK ) {
            return false; // commented because it can happen when it's not used correctly by the user //throw "Internal Error!";
        }

        // check if the last token was an EOF
        if( currentToken.type != EnumTokenType.EOF ) {
            // TODO< add line information and marker >

            // TODO< get the string format of the last token >
            throw "Unexpected Tokens after (Last) Token";
        }

        return true;
    }

    // /return success
    private function eatToken(): Bool {
        var lexerResultTuple = this.lexer.nextToken();

        this.currentToken = lexerResultTuple.resultToken;
        var lexerReturnValue: EnumLexerCode = lexerResultTuple.code;

        var success = lexerReturnValue == EnumLexerCode.OK;
        if( !success ) {
            return false;
        }

        if(ParserConfig.debugParser) this.currentToken.debugIt();

        this.addTokenToLines(this.currentToken.copy());

        return success;
    }

    public function addTokenToLines(token: Token<EnumOperationType>) {
        if( token.line != this.currentLineNumber ) {
            currentLineNumber = token.line;
            this.lines.push(new Line<EnumOperationType>());
        }

        this.lines[this.lines.length-1].tokens.push(token);
    }


    private var currentToken: Token<EnumOperationType>;

    public var arcs: Array<Arc<EnumOperationType>> = [];
    public var lexer: Lexer<EnumOperationType>;

    private var lines: Array<Line<EnumOperationType>>;
    private var currentLineNumber = 0;
}

enum EnumTokenType {
    NUMBER;
    IDENTIFIER;
    KEYWORD;       // example: if do end then
    OPERATION;     // example: := > < >= <=
      
    ERROR;         // if Lexer found an error
    STRING;        // "..."
      
    EOF;           // end of file
    // TODO< more? >
}

// TODO REFACTOR< build it as enum with content >
@generic
class Token<EnumOperationType> {
   public var type: EnumTokenType;

   public var contentString: String;
   public var contentOperation: Null<EnumOperationType> = null;
   public var contentNumber: Int = 0;

   public var line: Int = 0;

   public function new(type) {
       this.type = type;
   }
   
   public function debugIt() {
      trace("Type: " + type);

      if( type == EnumTokenType.OPERATION ) {
         trace("Operation: " + contentOperation);
      }
      else if( type == EnumTokenType.NUMBER ) {
         trace(contentNumber);
      }
      else if( type == EnumTokenType.IDENTIFIER ) {
         trace(contentString);
      }
      else if( type == EnumTokenType.STRING ) {
         trace(contentString);
      }

      trace("Line   : " + line);
      //trace("Column : " + column);

      trace("===");
   }

   public function copy(): Token<EnumOperationType> {
      var result = new Token<EnumOperationType>(this.type);
      result.contentString = this.contentString;
      result.contentOperation = this.contentOperation;
      result.contentNumber = this.contentNumber;
      result.line = this.line;
      //result.column = this.column;
      return result;
   }
}

enum EnumLexerCode {
    OK;
    INVALID;
}

@generic
class Lexer<EnumTokenOperationType> {
    public var remainingSource: String = null;

    // regex rules of tokens
    // token rule #0 is ignored, because it contains the pattern for spaces
    public var tokenRules: Array<String>;

    
    public function new() {}

    public function setSource(source: String) {
        this.remainingSource = source;
    }

    
    public function nextToken(): {resultToken: Token<EnumTokenOperationType>, code: EnumLexerCode} {
        while(true) {
            //size_t index;
            //EnumLexerCode lexerCode = nextTokenInternal(resultToken, index);
            var internalCalleeResult = nextTokenInternal();

            var resultToken = internalCalleeResult.resultToken;
            
            if (internalCalleeResult.resultCode != EnumLexerCode.OK) {
                return {resultToken: resultToken, code: internalCalleeResult.resultCode};
            }

            if (internalCalleeResult.index == 0) {
                continue;
            }

            if (resultToken.type == EnumTokenType.EOF) {
                return {resultToken: resultToken, code: internalCalleeResult.resultCode};
            }

            return {resultToken: resultToken, code: internalCalleeResult.resultCode};
        }
    }

    /*abstract*/ public function createToken(ruleIndex: Int, matchedString: String): Token<EnumTokenOperationType> {
        throw "Not implemented Abstract method called!";
    }


    private function nextTokenInternal(): {resultCode: EnumLexerCode, resultToken: Token<EnumTokenOperationType>, index: Null<Int>} {//out Token!EnumTokenOperationType resultToken, out size_t index) {
        var endReached = remainingSource.length == 0;
        if (endReached) {
            var resultToken = new Token<EnumTokenOperationType>(EnumTokenType.EOF);
            return {resultCode: EnumLexerCode.OK, resultToken: resultToken, index: null};
        }

        var iindex = 0;
        for (iterationTokenRule in tokenRules) {
            var r = new EReg(iterationTokenRule, "");
            if( r.match(remainingSource) ) {
                if (r.matchedPos().pos != 0) {
                    // is a bug because all matches must start at the beginning of the remaining string!
                    throw "Parsing error: position must be at the beginning!";
                }

                remainingSource = remainingSource.substring(r.matchedPos().len, remainingSource.length);

                var matchedString: String = r.matched(0);

                var resultToken = createToken(iindex, matchedString);
                return {resultCode: EnumLexerCode.OK, resultToken: resultToken, index: iindex};
            }
            iindex++;
        }

        if(ParserConfig.debugParser) trace("<INVALID>");
        return {resultCode: EnumLexerCode.INVALID, resultToken: null, index: null};
    }
}

// operation for narsese tokens
enum EnumOperationType {
	INHERITANCE; // -->
    SIMILARITY; // <->
	IMPLICATION; // ==>
	EQUIVALENCE; // <=>

	BRACEOPEN; // <
	BRACECLOSE; // >
	ROUNDBRACEOPEN; // (
	ROUNDBRACECLOSE; // )
    
	//KEY #

	QUESTIONVAR; // ?XXX
	INDEPENDENTVAR; // $XXX
	DEPENDENTVAR; // #XXX

    CURLBRACEOPEN; // {
    CURLBRACECLOSE; // }
    BRACKETOPEN; // [
	BRACKETCLOSE; // ]
	
    DOT; // .
    QUESTIONMARK; // ?
    //EXCLAMATIONMARK; // !
    //AT; // @
    STAR; // *
    SLASH; // "/"
    UNDERSCORE; // _
    AMPERSAND; // &
    PIPE; // |
    MINUS; // -

    //COMMA; // ,
    //DOUBLEAMPERSAND; // &&
    //AMPERSAND; // &


	//HALFH; // |-    
}

class NarseseLexer extends Lexer<EnumOperationType> {
    public function new() {
        super();

        tokenRules = [
            /*  0 */"^\\ ", // special token for space
            /*  1 */"^\\-\\->",
            /*  2 */"^<\\->",
            /*  3 */"^==>",
            /*  4 */"^<=>",
            /*  5 */"^<",
            /*  6 */"^>",

            /*  7 */"^\\(",
            /*  8 */"^\\)",

            /*  9 */"^\\?[a-zA-Z0-9_\\.]+",
            /* 10*/"^\\$[a-zA-Z0-9_\\.]+",
            /* 11*/"^#[a-zA-Z0-9_\\.]+",

            /* 12*/"^\\{",
            /* 13*/"^\\}",
            /* 14*/"^\\[",
            /* 15*/"^\\]",

            /* 16*/"^\\.",
            /* 17*/"^\\?",
            /* 18*/"^\\*",
            /* 19*/"^\\/",
            /* 20*/"^[a-z0-9A-Z_\\.]+", // identifier // TODO< other letters >
            /* 21*/"^\"[a-z0-9A-Z_!\\?:\\.,;\\ \\-\\(\\)\\[\\]{}<>]*\"", // string 

            /* 22*/"^\\_",
            /* 23*/"^&", // used for compounds
            /* 24*/"^\\|", // used for compounds
            /* 25*/"^-", // used for compounds
        ];
    }

    public override function createToken(ruleIndex: Int, matchedString: String): Token<EnumOperationType> {
        if(ParserConfig.debugParser) trace('CALL createToken w/  ruleIndex=$ruleIndex   matchedString=$matchedString@');
        
        switch (ruleIndex) { // switch on index of tokenRules
            case 0: // empty token
            return null;

            case 1:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.INHERITANCE;
            res.contentString = matchedString;
            return res;

            case 2:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.SIMILARITY;
            res.contentString = matchedString;
            return res;

            case 3:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.IMPLICATION;
            res.contentString = matchedString;
            return res;

            case 4:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.EQUIVALENCE;
            res.contentString = matchedString;
            return res;

            case 5:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.BRACEOPEN;
            return res;

            case 6:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.BRACECLOSE;
            return res;

            case 7:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.ROUNDBRACEOPEN;
            return res;

            case 8:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.ROUNDBRACECLOSE;
            return res;

            case 9:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.QUESTIONVAR;
            res.contentString = matchedString;
            return res;

            case 10:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.INDEPENDENTVAR;
            res.contentString = matchedString;
            return res;

            case 11:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.DEPENDENTVAR;
            res.contentString = matchedString;
            return res;

            case 12:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.CURLBRACEOPEN;
            res.contentString = matchedString;
            return res;

            case 13:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.CURLBRACECLOSE;
            res.contentString = matchedString;
            return res;

            case 14:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.BRACKETOPEN;
            res.contentString = matchedString;
            return res;

            case 15:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.BRACKETCLOSE;
            res.contentString = matchedString;
            return res;


            case 16:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.DOT;
            res.contentString = matchedString;
            return res;

            case 17:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.QUESTIONMARK;
            res.contentString = matchedString;
            return res;

            case 18:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.STAR;
            res.contentString = matchedString;
            return res;

            case 19:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.SLASH;
            res.contentString = matchedString;
            return res;

            case 20:
            var res = new Token<EnumOperationType>(EnumTokenType.IDENTIFIER);
            res.contentString = matchedString;
            return res;

            case 21:
            var res = new Token<EnumOperationType>(EnumTokenType.STRING);
            res.contentString = matchedString;
            return res;

            case 22:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.UNDERSCORE;
            res.contentString = matchedString;
            return res;

            case 23:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.AMPERSAND;
            res.contentString = matchedString;
            return res;

            case 24:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.PIPE;
            res.contentString = matchedString;
            return res;

            case 25:
            var res = new Token<EnumOperationType>(EnumTokenType.OPERATION);
            res.contentOperation = EnumOperationType.MINUS;
            res.contentString = matchedString;
            return res;

            default:
            throw 'Not implemented regex rule index=$ruleIndex!';
        }

        throw "Not implemented Abstract method called!";
    }
}

class NarseseParser extends Parser<EnumOperationType> {
    public var stack: Array<Term> = []; // stack used for parsing
    
    public function new() {
        super();
    }

    public override function convOperationToCode(op: EnumOperationType): Int {
        return switch (op) {
            case INHERITANCE: 1; // -->
            case SIMILARITY: 2; // <->
	        case IMPLICATION: 3; // ==>
	        case EQUIVALENCE: 4; // <=>

	        case BRACEOPEN: 5; // <
	        case BRACECLOSE: 6; // >

            case ROUNDBRACEOPEN: 7; // (
	        case ROUNDBRACECLOSE: 8; // )
	
	//KEY;
	        
            case QUESTIONVAR: 9; // ?XXX
            case INDEPENDENTVAR: 10; // $xxx
            case DEPENDENTVAR: 11; // #xxx

            case CURLBRACEOPEN: 12; // {
	        case CURLBRACECLOSE: 13; // }
            case BRACKETOPEN: 14; // [
	        case BRACKETCLOSE: 15; // ]

	//CONJUNCTION; // &&
            case DOT: 16; // .
            case QUESTIONMARK: 17; // ?
            case STAR: 18; // *
            case SLASH: 19; // "/"
            case UNDERSCORE: 22; // _
            case AMPERSAND: 23; // &
            case PIPE: 24; // |
            case MINUS: 25; // -
        }
    }
}

@generic
class Line<EnumOperationType> {
   public var tokens: Array<Token<EnumOperationType>> = [];

   public function new() {}
}

class ProtoLexer {
    public static function main() {
        // print printed terms to check right parsing manually
        var parseResults = [
            parse("<(a & b) --> x>."),
            parse("<(a & b & c) --> x>."),
            parse("<(a | b) --> x>."),
            parse("<(a | b | c) --> x>."),
            parse("<(a - b) --> x>."),

            // set
            parse("<{a} --> x>."),
            //parse("<{a b} --> x>."), // commented because multi sets are not supported

            parse("<x --> [a]>."),
            //parse("<x --> [a b]>."), // commented because multi sets are not supported


            parse("<{a} --> [b]>."),
            //parse("<{a b} --> [b]>."), // commented because multi sets are not supported


            parse("< a_ --><b --> c >  >."),
            parse("<a_.5--> b>?"),
            parse("<a_.5<-> b>?"),
            parse("<<c-->d>==> b>?"),
            parse("<<c-->d><=> <e-->f>>?"),

            // variables
            parse("<?x-->x>?"),
            parse("<$x-->x>."),
            parse("<#x-->x>."),

            parse("<\"abc\"-->x>."), // string
            parse("<\"a-b-c\"-->x>."), // string
            parse("<\"a b c\"-->x>."), // string
            parse("<\"!?.,:;][)(}{><\"-->x>."), // string

            // product
            parse("(a*b)."),
            parse("(a*b*c)."),
            parse("(a*b*c*d)."),
            parse("(<a-->c>*b)."),
            parse("(a*<b-->c>)."),
        ];
        for (iParseResult in parseResults) {
            trace(TermUtils.convToStr(iParseResult.term) + iParseResult.punctuation);
        }
    }
    public static function parse(narsese: String): {term: Term, punctuation: String, tvFreq:Null<Float>, tvConf:Null<Float>} {
        function statementBegin(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            if(ParserConfig.debugParser) trace("CALL statementBegin()");
        }

        function statementSetCopula(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            if(ParserConfig.debugParser) trace("CALL statementSetCopula()");

            var parser2 = cast(parser, NarseseParser);
            parser2.stack.push(Name(currentToken.contentString)); // WORKAROUND< push as name >
        }

        function statementEnd(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            if(ParserConfig.debugParser) trace("CALL statementEnd()");

            var parser2 = cast(parser, NarseseParser);

            // build statement from stack
            var pred = parser2.stack[parser2.stack.length-1];

            var copulaTerm = parser2.stack[parser2.stack.length-2]; // copula encoded as Name

            var copulaStr = "";
            switch (copulaTerm) {
                case Name(name):
                copulaStr = name;
                default:
                throw "Expected Name!"; // internal error
            }

            //var copulaStr = cast(parser2.stack[parser2.stack.length-2], Name).; // copula encoded as Name
            var subj = parser2.stack[parser2.stack.length-3];

            parser2.stack.pop();
            parser2.stack.pop();
            parser2.stack.pop();

            parser2.stack.push(Cop(copulaStr, subj, pred));
        }


        function statementStoreSubj(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            // stores subject
            
            if(ParserConfig.debugParser) trace("CALL statementStoreSubj()");
        }

        function statementStorePred(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            // stores predicate
            
            if(ParserConfig.debugParser) trace("CALL statementStorePred()");
        }


        function identifierStore(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            if(ParserConfig.debugParser) trace("CALL identifierStore()");

            var parser2 = cast(parser, NarseseParser);
            parser2.stack.push(Name(currentToken.contentString)); // push the identifier as a Name term to the stack
        }

        // store variable
        function varStore(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            if(ParserConfig.debugParser) trace("CALL varStore()");

            var parser2 = cast(parser, NarseseParser);
            
            var varType: String = currentToken.contentString.charAt(0);
            var varName: String = currentToken.contentString.substring(1, currentToken.contentString.length);
            parser2.stack.push(Var(varType, varName)); // push the variable
        }

        function stringStore(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            if(ParserConfig.debugParser) trace("CALL stringStore()");

            var parser2 = cast(parser, NarseseParser);
            parser2.stack.push(Str(currentToken.contentString.substring(1, currentToken.contentString.length-1))); // push the variable
        }

        var punctuation: String = null;
        // called to set the punctuation of this sentence
        function setPunctuation(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            if(ParserConfig.debugParser) trace("CALL setPunctuation()");

            punctuation = currentToken.contentString;
        }

        function roundBraceBegin(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            var parser2 = cast(parser, NarseseParser);
            parser2.stack.push(Name("(")); // HACK< simply push the content as a name >
                                           // TODO< we need a better solution here which is safe against bugs >
        }

        function roundBraceEnd(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            var parser2 = cast(parser, NarseseParser);

            if(ParserConfig.debugParser) {
                var idx = 0;
                for (iStackElement in parser2.stack) {
                    if(ParserConfig.debugParser) trace('roundBraceEnd()  stackContent[$idx] = ${TermUtils.convToStr(parser2.stack[idx])}');
                    idx++;
                }
            }
            
            // scan till the next "(" in stack and check if all seperators are the same, store content and create Prod
            var braceContent;
            {
                var braceContentStack: Array<Term> = []; // content of brace in reversed order

                var stackIdx = parser2.stack.length-1;
                var found = false;
                while (!found) {
                    var iStack: Term = parser2.stack[stackIdx]; // iterator value of stack
                    switch (iStack) {
                        case Name("("): // found "(" which is the beginning of the round brace
                        found = true;
                        case _:
                        braceContentStack.push(iStack);
                        stackIdx--;
                    }
                }

                // clean up stack and remove all elements till index
                parser2.stack = parser2.stack.slice(0, stackIdx);

                // invert order of stack to get real order
                braceContent = braceContentStack.copy();
                braceContent.reverse();
            }


            if(ParserConfig.debugParser) {
                trace("AFTER");

                var idx = 0;
                for (iStackElement in braceContent) {
                    trace('roundBraceEnd()  braceContent[$idx] = ${TermUtils.convToStr(iStackElement)}');
                    idx++;
                }
            }


            // now we need to decode the brace content

            if (braceContent.length < 2) {
                throw "Parsing failed: content in \"(\" ... \")\" must have at least two elements!";
            }

            // type of product, can be null if it is not known or "PROD" if it is a product
            var type = switch (braceContent[1]) {
                case Name("*"): // is product
                "*";
                case Name("&"):
                "&";
                case Name("|"):
                "|";
                case Name("-"):
                "-";
                case _:
                // TODO< better error message >
                throw "Parsing failed: content in \"(\" ... \")\" must be a product or conj/disj!"; // TODO< can also be a image >
            }

            if (braceContent.length%2 != 1) { // must be uneven
                throw "Parsing failed: invalid content of brace!";
            }

            // check type
            var idx = 1;
            while (idx < braceContent.length) {
                switch (braceContent[idx]) {
                    case Name(type2) if (type2 == type):
                    case _:
                    throw "Parsing failed: product elements must be seperated with * !";
                }
                idx+=2;
            }

            // enumerate content
            var productContent: Array<Term> = [];
            idx = 0;
            while (idx < braceContent.length) {
                switch (braceContent[idx]) {
                    case Name(type2) if (type2 == "*" || type2 == "&" || type2 == "|" || type2 == "-"):
                    throw 'Parsing failed: product elements must not be $type2 !';
                    case _:
                    productContent.push(braceContent[idx]);
                }
                idx+=2;
            }

            switch (type) {
                case "*": // is a product
                // build and return Prod(productContent) to stack
                parser2.stack.push(Prod(productContent));

                case type2 if (type2 == "&" || type2 == "|"): // is compound
                parser2.stack.push(Compound(type2, productContent));

                case "-": // is compound
                // check
                if (productContent.length != 2) {
                    throw 'Parsing failed: difference defined for two elements!';
                }
                parser2.stack.push(Compound("-", productContent));

                case _:
                throw "Internal error"; // TODO< remove with special enum >
            }
        }

        function tokenStore(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            var parser2 = cast(parser, NarseseParser);
            parser2.stack.push(Name(currentToken.contentString)); // HACK< simply push the content as a name >
                                                                  // TODO< we need a better solution here which is safe against bugs >
        }

        function braceSetEnd(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            var parser2 = cast(parser, NarseseParser);

            // scan till we hit the stored token for the set-beginning
            var braceContentStack: Array<Term> = []; // content of brace in reversed order

            var stackIdx = parser2.stack.length-1;
            var found = false;
            while (!found) {
                var iStack: Term = parser2.stack[stackIdx]; // iterator value of stack
                switch (iStack) {
                    case Name("{"): // found "{" which is the beginning of the round brace
                    found = true;
                    case _:
                    braceContentStack.push(iStack);
                    stackIdx--;
                }
            }
            
            // clean up stack and remove all elements till index
            parser2.stack = parser2.stack.slice(0, stackIdx);

            parser2.stack.push(Set("{", braceContentStack));
        }

        function bracketSetEnd(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            var parser2 = cast(parser, NarseseParser);
            
            // scan till we hit the stored token for the set-beginning
            var braceContentStack: Array<Term> = []; // content of brace in reversed order

            var stackIdx = parser2.stack.length-1;
            var found = false;
            while (!found) {
                var iStack: Term = parser2.stack[stackIdx]; // iterator value of stack
                switch (iStack) {
                    case Name("["): // found "{" which is the beginning of the round brace
                    found = true;
                    case _:
                    braceContentStack.push(iStack);
                    stackIdx--;
                }
            }
            
            // clean up stack and remove all elements till index
            parser2.stack = parser2.stack.slice(0, stackIdx);

            parser2.stack.push(Set("[", braceContentStack));
        }




        var lexer: NarseseLexer = new NarseseLexer();

        lexer.setSource(narsese);

        var parser: NarseseParser = new NarseseParser();
        parser.arcs = [
            /*   0 */new Arc<EnumOperationType>(EnumArcType.END, 0, null, -1, null), // global end arc
            /*   1 */new Arc<EnumOperationType>(EnumArcType.ARC, 20, null, 2, null),
            /*   2 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 16, setPunctuation, 0, 3), // .
            /*   3 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 17, setPunctuation, 0, null), // ?
            /*   4 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),

            /*   5 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*   6 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*   7 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*   8 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*   9 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),

            /*  10 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  11 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  12 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  13 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  14 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),

            /*  15 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  16 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  17 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  18 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  19 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),

            // decide between identifies, statement, vars, brace (for products, etc)
            /*  20 */new Arc<EnumOperationType>(EnumArcType.TOKEN, 1/*identifier*/, identifierStore, 29, 21),
            /*  21 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 5, null, 22, 23), // <
            /*  22 */new Arc<EnumOperationType>(EnumArcType.ARC, 40, null, 29, null),
            /*  23 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 9, varStore, 29, 24), // ?X
            /*  24 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 10, varStore, 29, 25), // $X

            /*  25 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 11, varStore, 29, 26), // #X
            /*  26 */new Arc<EnumOperationType>(EnumArcType.TOKEN, 5, stringStore, 29, 27), // "..."
            /*  27 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 7, null, 28, 30), // (
            /*  28 */new Arc<EnumOperationType>(EnumArcType.ARC, 60, null, 29, null),
            /*  29 */new Arc<EnumOperationType>(EnumArcType.END, 0, null, -1, null),

            /*  30 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 18, tokenStore, 0, 31), // "*" - is a seperator of a product, just store it
            /*  31 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 12, tokenStore, 32, 33), // "{" - we need to store token to know when the set ended
            /*  32 */new Arc<EnumOperationType>(EnumArcType.ARC, 80, null, 0, null),
            /*  33 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 14, tokenStore, 34, 35), // "[" - we need to store token to know when the set ended
            /*  34 */new Arc<EnumOperationType>(EnumArcType.ARC, 90, null, 0, null),

            /*  35 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 23, tokenStore, 0, 36), // "&" - is a seperator for compound, just store it
            /*  36 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 24, tokenStore, 0, 37), // "|" - is a seperator for compound, just store it
            /*  37 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 25, tokenStore, 0, null), // "-" - is a seperator for compound, just store it
            /*  38 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  39 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),

            // statement "<"pred copular subj">"
            // "<"" was already consumed
            /*  40 */new Arc<EnumOperationType>(EnumArcType.NIL  , 0, statementBegin, 41, null),
            /*  41 */new Arc<EnumOperationType>(EnumArcType.ARC  , 20, null, 42, null),
            /*  42 */new Arc<EnumOperationType>(EnumArcType.NIL  , 0, statementStoreSubj, 43, null),
            //    * dispatch for copula
            /*  43 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 1, statementSetCopula, 50, 44), // -->
            /*  44 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 2, statementSetCopula, 50, 45), // <->

            /*  45 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 3, statementSetCopula, 50, 46), // ==>
            /*  46 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 4, statementSetCopula, 50, null), // <=>
            /*  47 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  48 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  49 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),

            /*  50 */new Arc<EnumOperationType>(EnumArcType.ARC  , 20, null, 51, null),
            /*  51 */new Arc<EnumOperationType>(EnumArcType.NIL  , 0, statementStorePred, 52, null),
            /*  52 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 6, statementEnd, 53, null), // >
            /*  53 */new Arc<EnumOperationType>(EnumArcType.END  , 0, null, -1, null),
            /*  54 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),

            /*  55 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  56 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  57 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  58 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  59 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),

            // round brace enclosed term, "(" ??? ")", can be product or image, etc
            // "(" was already consumed
            /*  60 */new Arc<EnumOperationType>(EnumArcType.NIL  , 0, roundBraceBegin, 61, null),
            /*  61 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 8, roundBraceEnd, 0, 62), // ")" round brace finished                 //new Arc<EnumOperationType>(EnumArcType.ARC, 20, null, 62, null), // expect next arc with term
            /*  62 */new Arc<EnumOperationType>(EnumArcType.ARC  , 20, null, 61, null), // something else       //new Arc<EnumOperationType>(EnumArcType.OPERATION, 8, roundBraceEnd, 63, 64), // term finished, expect either ")" or "*"
            /*  63 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),                          //new Arc<EnumOperationType>(EnumArcType.END, 0, null, -1, null), // finished "(" ... ")"
            /*  64 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),                            //  new Arc<EnumOperationType>(EnumArcType.OPERATION, 14, roundBraceSeperator, 61, null), // check for "*" as the seperator

            /*  65 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  66 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  67 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  68 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  69 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),

            /*  70 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  71 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  72 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  73 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  74 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),

            /*  75 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  76 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  77 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  78 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  79 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),

            // { } set, "{" was already consumed
            /*  80 */new Arc<EnumOperationType>(EnumArcType.ARC  , 20, null, 81, null),
            /*  81 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 13, braceSetEnd, 0, null), // "}" 
            /*  82 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  83 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  84 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),

            /*  85 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  86 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  87 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  88 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  89 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),


            // [ ] set, "[" was already consumed
            /*  90 */new Arc<EnumOperationType>(EnumArcType.ARC  , 20, null, 91, null),
            /*  91 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 15, bracketSetEnd, 0, null), // "]"
            /*  92 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  93 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  94 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),

            /*  95 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  96 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  97 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  98 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  99 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),


        ];

        parser.lexer = lexer;

        var parsingSuccess: Bool = parser.parse();
        if (!parsingSuccess) {
            throw "Parsing failed!";
        }

        if (parser.stack.length != 1) {
            throw "Parsing failed! Number of elements on stack != 1";
        }

        var resultTerm: Term = parser.stack[0];

        return {term:resultTerm, punctuation:punctuation, tvFreq:null, tvConf:null};
    }
}

// parser configuration
class ParserConfig {
    public static var debugParser: Bool = false;
}



// TODO< negative parsing tests for braces >
//    TODO< negative test "(a)" // products with one element are not valid
//    TODO< negative test "(."
//    TODO< negative test "()."
//    TODO< negative test "(*."
//    TODO< negative test "(*b."
//    TODO< negative test "(a*)."
//    TODO< negative test "(a*b#)." // test for not equal seperators
//    TODO< negative test "(a*b#c)." // test for not equal seperators
//    TODO< negative test "(a b)." // product without seperator is not allowed
//    TODO< negative test "(*)."
//    TODO< negative test ")."


// TODO< add support for images in parser grammar >
// TODO< add support for images in parser brace function >


// TODO< add tv to parsing >
// TODO< add event occurence to parser >
