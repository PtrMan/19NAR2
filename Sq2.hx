/*
Copyright 2019 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

// run with
//    haxe --interp -main Sq2.hx


// TODO< remove comments with "//" before lexing >

// TODO< parse TV >
// TODO< test parsing of TV >



// TODO BUG< do revision on input processing time too >

// TODO< implement Unifier.containsVar() and unittest >

// basic attention
//     TODO OUTDATED< attention mechanism : sort after epoch and limit size for next epoch >
//     TODO   < lazy update of propability mass after processing task >

// TODO< test attention mechanism with other examples from ALANN >


// TODO< attention mechansim : questions have way higher priority than judgments >

// TODO< attention mechanism : stresstest attention >

// TODO< backward derivation >

// TODO< keep concepts(nodes) under AIKR (by calculating the max exp() and throwing the concepts out with lowest max exp() >

// TODO< keep tasks under AIKR (by sorting by score(utility) and slicing)

// TODO CONTINUE IMPL< most NAL-2 like in new meta rules >



// TODO< check if it builds and implement if not derived:
// <shape1 --> rectangle>.
// <shape1 --> [filled]>.
// to
// <shape1 --> (&, rectangle, [filled])>


// TODO COMPLICATED< Q&A - do structural transformations on question side without adding the question to the memory or the tasks, sample all possible structural transformations and remember which transformations were done, etc >



// DONE< variables >

// DONE< structural transformation of <-> and <=> >
// DONE TEST< unittest structural transformation of <-> and <=> >

// DONE< rename to Node like in ALANN >

// DONE< structural transform from images back to products >
// DONE TEST< structural transform from images back to products >
// DONE TEST< structural transform from products to images >

// DONE< revision >

// DONE< equivalence structural transformation with two premises ded >
// ex:
// <<$x-->d> <=> <$x-->e>>. [2]
// <c-->d>. [1]
// |-
// <c-->e>. [1]
// DONE< impl structural transformation with two premises ded >
// ex:
// <<$x-->d> ==> <$x-->e>>. [2]
// <c-->d>. [1]
// |-
// <c-->e>. [1]

// DONE< ATTENTION - probabilistic selection of task by probability mass >

// DONE< ATTENTION - test attention mechanism with A-->I example from ALANN >


// DONE< structural decomposition >
//<(*,a,b) --> (*,c,d)>.
//|-
//<a-->c>.
// (and other forms)
//
//<(*,a,b) <-> (*,c,d)>.
//|-
//<a<->c>.
// (and other forms)




// TODO< safe structuralOrigins correctly by appending >
class Sq2 {
    public var mem:Memory = new Memory();

    // working set of tasks
    public var workingSet:WorkingSet = new WorkingSet();

    // used for debugging and unittesting
    // set to null to disable adding conclusions to this array
    public var conclusionStrArr:Array<String> = null;

    public var stampIdCounter = haxe.Int64.make(0, 0);

    public function new() {}

    // puts new input from the outside of the system into the system
    public function inputTerm(term:Term, tv:Tv, punctation:String) {
        var sentence = new Sentence(term, tv, new Stamp([stampIdCounter.copy()], new StructuralOriginsStamp([])), punctation);
        stampIdCounter = haxe.Int64.add(stampIdCounter, haxe.Int64.make(0,1));

        if (punctation == ".") { // only add to memory for judgments
            mem.updateConceptsForJudgment(sentence);
        }

        var workingSetEntity = new WorkingSetEntity(sentence);

        workingSet.append(workingSetEntity);
    }

    // puts new narsese input from the outside into the system
    public function input(narsese:String) {
        var parseResult = ProtoLexer.parse(narsese);

        var tv = new Tv(1.0, 0.9); // standard TV
        if (parseResult.tvFreq != null) {
            tv.freq = parseResult.tvFreq;
            tv.conf = parseResult.tvConf;
        }

        inputTerm(parseResult.term, tv, parseResult.punctuation);
    }

    // run the reasoner for a number of cycles
    public function process(cycles:Int = 20) {
        function reportAnswer(sentence:Sentence) {
            var str = 'Answer:[  ?ms]${sentence.convToStr()}'; // report with ALANN formalism
            trace(str);

            if (conclusionStrArr != null) { // used for debugging and unittesting
                conclusionStrArr.push(str);
            }

            if (answerHandler != null) {
                answerHandler.report(sentence);
            }
        }

        var cycleCounter = -1;
        while(true) { // main loop
            cycleCounter++;

            if (cycleCounter > cycles) {
                break;
            }

            if (Config.debug_derivations)   trace("");
            if (Config.debug_derivations)   trace("");
            if (Config.debug_derivations)   trace("");

            if (workingSet.entities.length == 0) {
                continue; // nothing to work on, continue
            }

            // select random element from working set
            var chosenWorkingSetEntity;
            { // select element from working set by probabilistic selection by mass
                var probabilityMass: Float = workingSet.entities[workingSet.entities.length-1].accuScore;
                var chosenMass: Float = Math.random() * probabilityMass;

                var idx:Int = workingSet.calcIdxByScoreMass(chosenMass); ///////Std.random(workingSet.entities.length);
                chosenWorkingSetEntity = workingSet.entities[idx];
            }

            var premiseSentence = chosenWorkingSetEntity.sentence;

            // Q&A
            if (premiseSentence.punctation == "?") {
                // enumerate subterms
                // checked terms for enumeration of subterms of question
                var checkedTerms = TermUtils.enumTerms(premiseSentence.term);

                for (iTermName in checkedTerms) {
                    // try to retrieve concept
                    if (!mem.hasConceptByName(TermUtils.convToStr(iTermName))) {
                        continue;
                    }
                    var nodeOfTerm: Node = mem.retConceptByName(TermUtils.convToStr(iTermName));

                    // try to find better answer
                    for (iBelief in nodeOfTerm.judgments) {
                        if (iBelief.tv.exp() > chosenWorkingSetEntity.bestAnswerExp && Unifier.checkUnify(premiseSentence.term, iBelief.term) ) {
                            // found a better answer
                            chosenWorkingSetEntity.bestAnswerExp = iBelief.tv.exp();
                            reportAnswer(iBelief);
                        }
                    }
                }
            }

            var premiseTerm = chosenWorkingSetEntity.sentence.term;
            var premiseTermStructuralOrigins = chosenWorkingSetEntity.sentence.stamp.structuralOrigins.arr;
            var premiseTv = chosenWorkingSetEntity.sentence.tv;
            var premisePunctation = chosenWorkingSetEntity.sentence.punctation;
            var premiseStamp = chosenWorkingSetEntity.sentence.stamp;
            var conclusionsSinglePremise = deriveSinglePremise(premiseTerm, premiseTermStructuralOrigins, premiseTv, premisePunctation, premiseStamp);

            var conclusionsTwoPremises = [];
            { // two premise derivation

                var selectedSecondaryPremiseTerm;
                { // select random subterm of premiseTerm
                    var subterms:Array<Term> = TermUtils.enumTerms(premiseTerm);
                    var idx = Std.random(subterms.length);
                    selectedSecondaryPremiseTerm = subterms[idx];
                }

                // select random secondary premise
                var primaryConcept = mem.retConceptByName(TermUtils.convToStr(selectedSecondaryPremiseTerm));
                if (primaryConcept != null && primaryConcept.judgments.length > 0) {
                    if (Config.debug_derivations)   trace("two premise derivation !");

                    var secondaryIdx = Std.random(primaryConcept.judgments.length);
                    var secondarySentence = primaryConcept.judgments[secondaryIdx];

                    var secondaryTerm = secondarySentence.term;
                    var secondaryTv = secondarySentence.tv;
                    var secondaryPunctation = secondarySentence.punctation;
                    var secondaryStamp = secondarySentence.stamp;

                    if (Config.debug_derivations)   trace("inf   " +  TermUtils.convToStr(premiseTerm) +     "   ++++    "+TermUtils.convToStr(secondaryTerm));

                    if (!Stamp.checkOverlap(premiseStamp, secondaryStamp)) {
                        if (premisePunctation == "." && secondaryPunctation == "." && TermUtils.equal(premiseTerm, secondaryTerm)) { // can do revision
                            var tv = Tv.revision(premiseTv, secondaryTv);
                            var mergedStamp = Stamp.merge(premiseStamp, secondaryStamp);
                            var revisedSentence = new Sentence(premiseTerm, tv, mergedStamp, ".");
                            primaryConcept.judgments[secondaryIdx] = revisedSentence;

                            { // print and add for debugging
                                var conclusionAsStr = TermUtils.convToStr(premiseTerm) +  premisePunctation+" " + tv.convToStr();
                                if (Config.debug_derivations)   trace(conclusionAsStr);

                                if (conclusionStrArr != null) { // used for debugging and unittesting
                                    conclusionStrArr.push(conclusionAsStr);
                                }
                            }
                        }
                        else { // can't do revision, try normal inference
                            var conclusionsTwoPremisesAB = deriveTwoPremise(premiseTerm, premiseTv, premisePunctation, premiseStamp,   secondaryTerm, secondaryTv, secondaryPunctation, secondaryStamp);
                            var conclusionsTwoPremisesBA = deriveTwoPremise(secondaryTerm, secondaryTv, secondaryPunctation, secondaryStamp,   premiseTerm, premiseTv, premisePunctation, premiseStamp);
                            conclusionsTwoPremises = [].concat(conclusionsTwoPremisesAB).concat(conclusionsTwoPremisesBA);
                        }
                    }
                    else {
                        if (Config.debug_derivations)   trace('   stampOverlap a=${premiseStamp.ids.map(v -> haxe.Int64.toStr(v))}  b=${secondaryStamp.ids.map(v -> haxe.Int64.toStr(v))}');
                    }
                }
            }

            var conclusions = [].concat(conclusionsSinglePremise).concat(conclusionsTwoPremises);

            // filter out invalid statments like a-->a and a<->a
            conclusions = conclusions.filter(iConclusion -> {
                return switch (iConclusion.term) {
                    case Cop(copula,a,b) if((copula == "-->" || copula == "<->" || copula == "==>" || copula == "<=>") && TermUtils.equal(a,b)):
                    false;
                    case _: true;
                };
            });

            if (Config.debug_derivations)   trace("|-");
            for (iConclusion in conclusions) {
                var conclusionAsStr = TermUtils.convToStr(iConclusion.term) +  iConclusion.punctation+" " + iConclusion.tv.convToStr();
                if (Config.debug_derivations)   trace(conclusionAsStr);

                if (conclusionStrArr != null) { // used for debugging and unittesting
                    conclusionStrArr.push(conclusionAsStr);
                }
            }



            if (Config.debug_derivations)   trace("");
            if (Config.debug_derivations)   trace("");
            if (Config.debug_derivations)   trace("");


            // put conclusions back into working set
            for (iConclusion in conclusions) {
                var sentence = new Sentence(iConclusion.term, iConclusion.tv, iConclusion.stamp, iConclusion.punctation);

                var workingSetEntity = new WorkingSetEntity(sentence);
                
                // try to find conclusion in working set and add only if it doesn't yet exist
                var existsSentenceInWorkingSet = false;
                for (iWorkingSetEntity in workingSet.entities) {
                    if (Sentence.equal(iWorkingSetEntity.sentence, sentence)) {
                        existsSentenceInWorkingSet = true;
                        break;
                    }
                }
                
                if (!existsSentenceInWorkingSet) {
                    workingSet.append(workingSetEntity);
                }
            }

            // store conclusions
            for (iConclusion in conclusions) {
                var sentence = new Sentence(iConclusion.term, iConclusion.tv, iConclusion.stamp, iConclusion.punctation);
                mem.updateConceptsForJudgment(sentence);
            }

            
        }

        var numberOfConcepts = 0;
        {
            for (iConceptName in mem.conceptsByName.keys()) {
                numberOfConcepts++;
            }
        }

        if (Config.debug_derivations)   trace("Summary: ");
        if (Config.debug_derivations)   trace('   #concepts= $numberOfConcepts');
        if (Config.debug_derivations)   trace('   #workingset.entities= ${workingSet.entities.length}');


    }
    

    public static function deriveTwoPremise(premiseATerm:Term,premiseATv:Tv,premiseAPunctation:String,premiseAStamp:Stamp,  premiseBTerm:Term,premiseBTv:Tv,premiseBPunctation:String,premiseBStamp:Stamp) {
        
        // checks if term is a set
        function checkSet(t:Term):Bool {
            return false; // TODO< implement >
        }
        
        // see Narjurue
        function checkNoCommonSubterm(a:Term, b:Term):Bool {
            return true; // TODO< implement >
        }

        // reduces/foldes term
        // ex: ( a & b & (a & c) )  ====>  ( a & b & c )
        function fold(foldedType:String, extInt:Term):Term {
            var terms = [];

            function processRec(term) {
                switch (term) {
                    case Term.Compound(foldedType,content):
                    for (iContent in content) {
                        processRec(iContent);
                    }
                    case _:
                    if (!Utils.contains(terms, term)) {
                        terms.push(term);
                    }
                }
            }
            processRec(extInt);

            return Compound(foldedType, terms);
        }

        var mergedStamp = Stamp.merge(premiseAStamp, premiseBStamp);

        var conclusions:Array<{term:Term, tv:Tv, punctation:String, stamp:Stamp, ruleName:String}> = [];

        // call to generated code for deriver
        Deriver.inferenceCode(premiseATerm, premiseAPunctation, premiseATv, premiseBTerm, premiseBPunctation, premiseBTv, mergedStamp, conclusions);



        if (premiseAPunctation == "." && premiseBPunctation == ".") {

            // NAL-2 inspired by metaGen.py
            {
                // TODO< autogenerate code here >

                var copulaTypes = [
                    {copAsym:"-->",copSym:"<->",ConjCops:["& "],DisjCop:"| ",MinusCops:["-","~"]}
                ];

                for (iCopulaInfo in copulaTypes) {
                    var copAsym = iCopulaInfo.copAsym;
                    var copSym = iCopulaInfo.copSym;

                    var copAsymZ = copAsym; // TODO< replace time >

                    switch (premiseATerm) {
                        case Cop(copAsym0, a0, b0) if (copAsym0 == copAsym):

                        switch (premiseBTerm) {
                            case Cop(copAsymZ0, b1, c) if (copAsymZ0 == copAsym && TermUtils.equal(b0,b1)):

                            // print ("(A "+copAsym+" B),\t(B "+copAsymZ+" C)\t\t\t|-\t(A "+ival(copAsym,"t+z")+" C)\t\t(Truth:Deduction"+OmitForHOL(", Desire:Strong")+")")
                            //var conclusionTerm = Cop(copAsym, a0, c);
                            //commented because handled by syllogistic code  //conclusions.push({term:conclusionTerm, tv:Tv.deduction(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-2.two ded"});
                            
                            case Cop(copAsymZ0, c, b1) if (copAsymZ0 == copAsym && TermUtils.equal(b0,b1)):

                            // print ("(A "+copAsym+" B),\t(C "+copAsymZ+" B)\t\t\t|-\t(A "+copAsym+" C)\t\t(Truth:Induction"+IntervalProjection+OmitForHOL(", Desire:Weak")+")")
                            //var conclusionTerm = Cop(copAsym, a0, c);
                            //commented because handled by syllogistic code  conclusions.push({term:conclusionTerm, tv:Tv.induction(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-2.two ind"});
                            
                            case Cop(copAsymZ0, a1, c) if (copAsymZ0 == copAsym && TermUtils.equal(a0,a1)):

                            // print ("(A "+copAsym+" B),\t(A "+copAsymZ+" C)\t\t\t|-\t(B "+copAsym+" C)\t\t(Truth:Abduction"+IntervalProjection+OmitForHOL(", Desire:Strong")+")")
                            var conclusionTerm = Term.Cop(copAsym, a0, c);
                            conclusions.push({term:conclusionTerm, tv:Tv.abduction(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-2.two abd"});

                            case _:null;

                        }

                        if (copSym != null) {
                            var copSymZ = copSym; //.replace("t","z");

                            switch (premiseBTerm) {                                
                                case Cop(copSymZ0, c, b1) if (copSymZ0 == copSym && TermUtils.equal(b0,b1)):

                                //print ("(A "+copAsym+" B),\t(C "+copSymZ+" B)\t\t\t|-\t(A "+copAsym+" C)\t\t(Truth:Analogy"+IntervalProjection+OmitForHOL(", Desire:Strong")+")")
                                var conclusionTerm = Term.Cop(copAsym, a0, c);
                                conclusions.push({term:conclusionTerm, tv:Tv.analogy(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-2.two ana1"});

                                case Cop(copSymZ0, c, a1) if (copSymZ0 == copSym && TermUtils.equal(a0,a1)):

                                //print ("(A "+copAsym+" B),\t(C "+copSymZ+" A)\t\t\t|-\t(C "+ival(copSym,"t+z")+" B)\t\t(Truth:Analogy"+OmitForHOL(", Desire:Strong")+")")
                                var conclusionTerm = Term.Cop(copSym, c, b0);
                                conclusions.push({term:conclusionTerm, tv:Tv.analogy(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-2.two ana2"});


                                // TODO
                                //print ("(A "+copAsym+" B),\t(C "+copSymZ+" B)\t\t\t|-\t(A "+copSym+" C)\t\t(Truth:Comparison"+IntervalProjection+OmitForHOL(", Desire:Weak")+")")
                                //print ("(A "+copAsym+" B),\t(A "+copSymZ+" C)\t\t\t|-\t(C "+copSym+" B)\t\t(Truth:Comparison"+IntervalProjection+OmitForHOL(", Desire:Weak")+")")                    

                                case _:null;
                            }
                        }

                        case _:null;
                    }

                    switch (premiseATerm) {
                        case Cop(copSym, a0, b0):


                        if (copSym != null) {
                            var copSymZ = copSym; //.replace("t","z");

                            switch (premiseBTerm) {                        
                                case Cop(copAsymZ0, b1, c) if (copAsymZ0 == copAsym && TermUtils.equal(b0,b1)):

                                //print ("(A "+copSym+" B),\t(B "+copSymZ+" C)\t\t\t|-\t(A "+ival(copSym,"t+z")+" C)\t\t(Truth:Resemblance"+OmitForHOL(", Desire:Strong")+")")
                                var conclusionTerm = Term.Cop(copSym, a0, c);
                                conclusions.push({term:conclusionTerm, tv:Tv.resemblance(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-2.two res"});

                                case _: null;
                            }
                        }

                        case _: null;
                    }
                }
            }

            // NAL-3 union, intersection
            switch (premiseATerm) {
                case Cop("-->", subjA, predA):

                switch (premiseBTerm) {
                    case Cop("-->", subjB, predB) if (TermUtils.equal(predA, predB) && !TermUtils.equal(subjA, subjB) && !checkSet(subjA) && !checkSet(subjB) && checkNoCommonSubterm(subjA, subjB)):

                    {
                        // #R[(P --> M) (S --> M) |- ((S & P) --> M) :post (:t/union))
                        var conclusionSubj = fold("&", Compound("&",[subjA, subjB]));
                        var conclusionTerm = Term.Cop("-->", conclusionSubj, predA);
                        conclusions.push({term:conclusionTerm, tv:Tv.union(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-3.two union"});
                    }

                    {
                        // #R[(P --> M) (S --> M) |- ((S | P) --> M) :post (:t/intersection)
                        var conclusionSubj = fold("|", Compound("|",[subjA, subjB]));
                        var conclusionTerm = Term.Cop("-->", conclusionSubj, predA);
                        conclusions.push({term:conclusionTerm, tv:Tv.intersection(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-3.two intersection"});
                    }


                    case _: null;
                }

                case _: null;
            }            
        }



        // merge set
        function setMerge(a:Array<Term>, b:Array<Term>): Array<Term> {
            var merged = a;

            for(iB in b) {
                var hasB = merged.filter(iMerged -> TermUtils.equal(iMerged, iB)).length > 0;
                if (!hasB) {
                    merged.push(iB);
                }
            }

            return merged;
        }

        // set handling
        if (premiseAPunctation == "." && premiseBPunctation == ".") {
            switch(premiseATerm) {
                case Cop(copA, Set("{", setA), predA):


                switch(premiseBTerm) {
                    case Cop(copB, Set("{", setB), predB):
                    if ((copA == "-->" || copA == "<->") && copA == copB && TermUtils.equal(predA, predB)) {
                        // <{a}-->c>.
                        // <{b}-->c>.
                        // |-
                        // <{b a}-->c>.
                        var mergedSet:Array<Term> = setMerge(setA, setB);
                        var conclusionTerm = Term.Cop(copA, Term.Set("{", mergedSet), predA);
                        conclusions.push({term:conclusionTerm, tv:Tv.intersection(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"set union"});
                    }
                    
                    case _:
                }
                case _:
            }


            switch(premiseATerm) {
                case Cop(copA, subjA, Set("[", setA)):


                switch(premiseBTerm) {
                    case Cop(copB, subjB, Set("[", setB)):
                    if ((copA == "-->" || copA == "<->") && copA == copB && TermUtils.equal(subjA, subjB)) {
                        // <c-->[a]>.
                        // <c-->[b]>.
                        // |-
                        // <c-->[b a]>.
                        var mergedSet:Array<Term> = setMerge(setA, setB);
                        var conclusionTerm = Term.Cop(copA, subjA, Term.Set("[", mergedSet));
                        conclusions.push({term:conclusionTerm, tv:Tv.intersection(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"set union"});
                    }
                    
                    case _:
                }
                case _:
            }
        } 






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

        


        /* commented because BS
        if (premiseAPunctation == "?" && premiseBPunctation == ".") {
            switch (premiseATerm) {
                // rule for helping with backward inference of implication
                // (&&, A, B)?
                // Z.
                // |-  if unifies(A,Z,AZ, "indep")
                // (&&, AZ, B).
                // (&&, AZ, B)?
                case Compound("&&", [a, b]) if (unifiesWithReplace(a, premiseBTerm, "indep") != null):
                var az:Term = unifiesWithReplace(a, premiseBTerm, "indep");
                conclusions.push({term:az, tv:null, punctation:"?", structuralOrigins:[], ruleName:"NAL-6.two conj q&a 1"});
                conclusions.push({term:az, tv:premiseBTv, punctation:".", structuralOrigins:[], ruleName:"NAL-6.two conj q&a 1"});
            

                // rule for helping with backward inference of implication
                // (&&, A, B)?
                // Z.
                // |-  if unifies(B,Z,BZ, "indep")
                // (&&, A, BZ).
                // (&&, A, BZ)?
                case Compound("&&", [a, b]) if (unifiesWithReplace(b, premiseBTerm, "indep") != null):
                var bz:Term = unifiesWithReplace(b, premiseBTerm, "indep");
                conclusions.push({term:bz, tv:null, punctation:"?", structuralOrigins:[], ruleName:"NAL-6.two conj q&a 2"});
                conclusions.push({term:bz, tv:premiseBTv, punctation:".", structuralOrigins:[], ruleName:"NAL-6.two conj q&a 2"});

                case _: null;
            }
        }
        */

        /* commented because it is BS because the conjuction has to talk about common sub-terms
        if (premiseAPunctation == "." && premiseBPunctation == ".") {
            // rule for forward inference of implication (detachment)
            //ex:
            // (&&, <({0} * $0) --> x>, <({1} * $1) --> y>) ==> <($0 * $1) --> c>.
            // (&&, <({0} * X) --> x>, <({1} * Y) --> y>).
            // |-
            // <(X * Y) --> c>.
            switch (premiseATerm) {
                case Cop("==>", Compound("&&", [compoundA0, compoundA1]), implPred):
                switch (premiseBTerm) {
                    case Compound("&&", [compoundB0, compoundB1]):

                    // TODO< handle variable assignment correctly >
                    var unified0:Term = unifiesWithReplace(compoundA0, compoundB0, "dep");
                    var unified1:Term = unifiesWithReplace(compoundA1, compoundB1, "dep");
                    
                    if (unified0 != null && unified1 != null) { // check if unification results are valid


                        // TODO< apply variable substition from unification >
                        var unifiedImplPred = implPred; // the predicate with the unified variables

                        trace("---");
                        trace('DEBUG   NAL6-two impl  ${TermUtils.convToStr(unified0)}');
                        trace('DEBUG   NAL6-two impl  ${TermUtils.convToStr(unified1)}');
                        trace('DEBUG   NAL6-two impl  |- ${TermUtils.convToStr(unifiedImplPred)}');

                        conclusions.push({term: unifiedImplPred, tv:Tv.deduction(premiseATv, premiseBTv), punctation:".", structuralOrigins:[], ruleName:"NAL6-two impl detach"});
                    }


                    case _: null;
                }

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
                    conclusions.push({term: conclusion, tv:Tv.deduction(premiseATv, premiseBTv)/*TODO check*/, punctation:".", stamp:mergedStamp, ruleName:"NAL6-two impl ==> detach conj[0]"});
                }

                // TODO< var unification >
                // ex:
                // <(&&,<a --> x>,<c --> x>) ==> <X --> Y>>.
                // <c-->x>.
                // |-
                // <a --> x> ==> <X --> Y>.
                if (TermUtils.equal(compoundA1, premiseBTerm)) {
                    var conclusion = Term.Cop("==>", compoundA0, implPred);
                    conclusions.push({term: conclusion, tv:Tv.deduction(premiseATv, premiseBTv)/*TODO check*/, punctation:".", stamp:mergedStamp, ruleName:"NAL6-two impl ==> detach conj[1]"});
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
                    conclusions.push({term: conclTerm, tv:Tv.deduction(premiseATv, premiseBTv)/*TODO check*/, punctation:".", stamp:premiseBStamp, ruleName:"NAL6-two impl structural transformation with two premises"});
                }

                case _: null;
            }
        }


        return conclusions;
    }

    // single premise derivation
    public static function deriveSinglePremise(premiseTerm:Term,premiseTermStructuralOrigins:Array<Term>,premiseTv:Tv,premisePunctation:String, premiseStamp:Stamp) {

        // we store the structural origin to avoid doing the same conversion over and over again
        var conclusions:Array<{term:Term, tv:Tv, punctation:String, stamp:Stamp, ruleName:String}> = [];

        

        // NAL-2 conversion
        if (premisePunctation == ".") switch (premiseTerm) {
            case Cop(copula, subj, pred) if (copula == "-->"):

            // TODO< bump derivation depth >
            
            var conclusionTerm = Term.Cop(copula, pred,subj);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                conclusions.push({term:conclusionTerm, tv:Tv.conversion(premiseTv), punctation:".", stamp:new Stamp(premiseStamp.ids, structuralOrigins), ruleName:"NAL-2.single contraposition"});
            }

            case _: null;
        }

        // NAL-2 <-> / NAL-6 <=> structural transformation
        if (premisePunctation == ".") switch (premiseTerm) {
            case Cop(copula, subj, pred) if (copula == "<->" || copula == "<=>"):

            // TODO< bump derivation depth >
            
            var conclusionTerm = Term.Cop(copula, pred,subj);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                conclusions.push({term:conclusionTerm, tv:premiseTv, punctation:".", stamp:new Stamp(premiseStamp.ids, structuralOrigins), ruleName:(copula == "<->" ? "NAL-2" : "NAL-6") + ".single structural"});
            }

            case _: null;
        }


        // NAL-4  product to image transform
        if (premisePunctation == ".") switch (premiseTerm) {
            case Cop("-->", Prod([prod0, prod1]), inhPred):

            // TODO< bump derivation depth >

            var conclusionTerm = Term.Cop("-->", prod0, Img(inhPred, [ImgWild, prod1]));
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                // <prod0 --> (/,inhPred,_,prod1)>
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                conclusions.push({term:conclusionTerm, tv:premiseTv, punctation:".", stamp:new Stamp(premiseStamp.ids, structuralOrigins), ruleName:"NAL-6.single prod->img"});
            }

            conclusionTerm = Term.Cop("-->", prod1, Img(inhPred, [prod0, ImgWild]));
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions

                // <prod1 --> (/,inhPred,prod0,_)>
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                conclusions.push({term:conclusionTerm, tv:premiseTv, punctation:".", stamp:new Stamp(premiseStamp.ids, structuralOrigins), ruleName:"NAL-6.single prod->img"});
            }

            case _: null;
        }

        // NAL-4  image to product transform
        if (premisePunctation == ".") switch (premiseTerm) {
            case Cop("-->", inhSubj, Img(inhPred, [ImgWild, prod1])):

            // TODO< bump derivation depth >

            var conclusionTerm = Term.Cop("-->", Prod([inhSubj, prod1]), inhPred);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                // <(*, inhSubj, prod1) --> inhPred>
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                conclusions.push({term:conclusionTerm, tv:premiseTv, punctation:".", stamp:new Stamp(premiseStamp.ids, structuralOrigins), ruleName:"NAL-6.single img->prod"});
            }


            case Cop("-->", inhSubj, Img(inhPred, [prod0, ImgWild])):

            // TODO< bump derivation depth >

            var conclusionTerm = Term.Cop("-->", Prod([prod0, inhSubj]), inhPred);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                // <(*, prod0, inhSubj) --> inhPred>
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                conclusions.push({term:conclusionTerm, tv:premiseTv, punctation:".", stamp:new Stamp(premiseStamp.ids, structuralOrigins), ruleName:"NAL-6.single img->prod"});
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

            // TODO< bump derivation depth >

            var conclusionTerms = [Term.Cop(cop, subj0, pred0), Term.Cop(cop, subj1, pred1)];
            
            for (iConclusionTerm in conclusionTerms) {
                if (!Utils.contains(premiseTermStructuralOrigins, iConclusionTerm)) { // avoid deriving the same structural conclusions
                    var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                    conclusions.push({term:iConclusionTerm, tv:premiseTv, punctation:".", stamp:new Stamp(premiseStamp.ids, structuralOrigins), ruleName:"NAL-6.single struct decomposition"});
                }
            }

            case _: null;
        }


        if (Config.debug_derivations)   trace(TermUtils.convToStr(premiseTerm)+premisePunctation);

        return conclusions;
        
    }


    public static function main() {
        

        /* TODO< add interesting unittest once it can build "&"
        { // create "seed" premise and put it into working set
            var premiseTerm:Term = Cop("-->", Prod([Name("a"), Name("a")]), Name("c"));
            var premiseTermStructuralOrigins:Array<Term> = [];
            var premiseTv:Tv = new Tv(1.0, 0.9);

            var sentence = new Sentence(premiseTerm, premiseTv, new Stamp(new StructuralOriginsStamp([])), ".");

            var workingSetEntity = new WorkingSetEntity(sentence);

            workingSet.entities.push(workingSetEntity);
        }
        */




        { // unittest set union
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // <z-->[c]>.
            // <z-->[d]>.
            // <z-->[c d]>.

            var unittestPremises:Array<Term> = [
                Cop("-->", Name("z"), Set("[",[Name("a")])),
                Cop("-->", Name("z"), Set("[",[Name("b")])),
            ];

            for (iUnittestPremise in unittestPremises) {
                reasoner.inputTerm(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process(20);

            if (reasoner.conclusionStrArr.indexOf("< z --> [a b] >. {1 0.81}", null) == -1) {
                throw "Unittest failed!";
            }
        }

        { // unittest set union
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // <{a}-->z>.
            // <{b}-->z>.
            // |-
            // <{b a}-->z>.

            var unittestPremises:Array<Term> = [
                Cop("-->", Set("{",[Name("a")]), Name("z")),
                Cop("-->", Set("{",[Name("b")]), Name("z")),
            ];

            for (iUnittestPremise in unittestPremises) {
                reasoner.inputTerm(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process(20);

            if (reasoner.conclusionStrArr.indexOf("< {a b} --> z >. {1 0.81}", null) == -1) {
                throw "Unittest failed!";
            }
        }


        { // unittest stamp overlap
            if (Stamp.checkOverlap(
                new Stamp([haxe.Int64.make(0, 0)], new StructuralOriginsStamp([])), 
                new Stamp([haxe.Int64.make(0, 1)], new StructuralOriginsStamp([])))
            ) {
                throw "Stamp overlap unittest (0) failed!";
            }

            if (!Stamp.checkOverlap(
                new Stamp([haxe.Int64.make(0, 1)], new StructuralOriginsStamp([])), 
                new Stamp([haxe.Int64.make(0, 1)], new StructuralOriginsStamp([])))
            ) {
                throw "Stamp overlap unittest (1) failed!";
            }

            if (!Stamp.checkOverlap(
                new Stamp([haxe.Int64.make(0, 2), haxe.Int64.make(0, 1)], new StructuralOriginsStamp([])), 
                new Stamp([haxe.Int64.make(0, 1)], new StructuralOriginsStamp([])))
            ) {
                throw "Stamp overlap unittest (2) failed!";
            }
            
        }

        { // unittest ded 
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            reasoner.input("<a --> b>.");
            reasoner.input("<b --> c>.");
            reasoner.input("<a --> c>?");
            // has to get answered

            reasoner.process(180); // needs a few more cycles

            trace("content:");

            for (iEntity in reasoner.workingSet.entities) {
                trace('   ${TermUtils.convToStr(iEntity.sentence.term)}${iEntity.sentence.punctation}  score=${iEntity.calcUtility()}');
            }
                


            if (reasoner.conclusionStrArr.indexOf("Answer:[  ?ms]< a --> c >. {1 0.81}", null) == -1) {
                trace("content:");

                for (iEntity in reasoner.workingSet.entities) {
                    trace('   ${TermUtils.convToStr(iEntity.sentence.term)}${iEntity.sentence.punctation}  score=${iEntity.calcUtility()}');
                }
                
                
                throw "Unittest failed!";
            }
        }

        { // unittest revision
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging


            var unittestPremises:Array<Term> = [
                Cop("-->", Name("a"),Name("b")),
                Cop("-->", Name("a"),Name("b")),
            ];

            for (iUnittestPremise in unittestPremises) {
                reasoner.inputTerm(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("< a --> b >. {1 0.94736842105263164}", null) == -1) {
                throw "Unittest failed!";
            }
        }

        { // unittest prod to img
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // <(a * b) --> prod>.
            // |-
            // <a --> (prod / _ b)>.
            // <b --> (prod / a _)>.

            var unittestPremises:Array<Term> = [
                Cop("-->", Prod([Name("a"),Name("b")]), Name("prod"))
            ];

            for (iUnittestPremise in unittestPremises) {
                reasoner.inputTerm(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("< a --> (/ prod _ b) >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }
            if (reasoner.conclusionStrArr.indexOf("< b --> (/ prod a _) >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }
        }

        { // unittest img to prod
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // <a --> (prod / _ b)>.
            // |-
            // <(a * b) --> prod>.

            var unittestPremises:Array<Term> = [
                Cop("-->", Name("a"), Img(Name("prod"), [ImgWild, Name("b")]))
            ];

            for (iUnittestPremise in unittestPremises) {
                reasoner.inputTerm(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("< ( a * b ) --> prod >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }
        }

        { // unittest img to prod
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // <b --> (prod / a _)>.
            // |-
            // <(a * b) --> prod>.

            var unittestPremises:Array<Term> = [
                Cop("-->", Name("b"), Img(Name("prod"), [Name("a"), ImgWild]))
            ];

            for (iUnittestPremise in unittestPremises) {
                reasoner.inputTerm(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("< ( a * b ) --> prod >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }
        }

        { // unittest NAL-4 structural decomposition
            // NAL-4 structural decomposition
            //<(*,a,b) --> (*,c,d)>.
            //|-
            //<a-->c>.
            // (and other forms)
            //
            
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            reasoner.input("<(a*b) --> (c*d)>.");
            reasoner.input("<a-->c>?");
            reasoner.input("<b-->d>?");
            // has to get answered

            reasoner.process(40); // needs a few more cycles


            if (reasoner.conclusionStrArr.indexOf("Answer:[  ?ms]< a --> c >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }

            if (reasoner.conclusionStrArr.indexOf("Answer:[  ?ms]< b --> d >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }
        }

        { // unittest NAL-4 structural decomposition
            // NAL-4 structural decomposition
            //<(*,a,b) <-> (*,c,d)>.
            //|-
            //<a<->c>.
            // (and other forms)
            
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            reasoner.input("<(a*b) <-> (c*d)>.");
            reasoner.input("<a<->c>?");
            reasoner.input("<b<->d>?");
            // has to get answered

            reasoner.process(40); // needs a few more cycles


            if (reasoner.conclusionStrArr.indexOf("Answer:[  ?ms]< a <-> c >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }

            if (reasoner.conclusionStrArr.indexOf("Answer:[  ?ms]< b <-> d >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }
        }

        { // unittest ==> detachment 
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // <(&&, <A --> x>, <B --> x>) ==> <Q --> c>>.
            // <A --> x>.
            // |-
            // <<B --> x> ==> <Q --> c>>.
            var unittestPremises:Array<Term> = [
                Cop("==>", Compound("&&", [Cop("-->", Name("A"), Name("x")), Cop("-->", Name("B"), Name("x"))]), Cop("-->", Name("Q"), Name("c"))),
                Cop("-->", Name("A"), Name("x"))
            ];

            for (iUnittestPremise in unittestPremises) {
                reasoner.inputTerm(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("< < B --> x > ==> < Q --> c > >. {1 0.81}", null) == -1) {
                throw "Unittest failed!";
            }

        }

        { // unittest ==> detachment 
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // <(&&, <A --> x>, <B --> x>) ==> <Q --> c>>.
            // <B --> x>.
            // |-
            // <<A --> x> ==> <Q --> c>.
            var unittestPremises:Array<Term> = [
                Cop("==>", Compound("&&", [Cop("-->", Name("A"), Name("x")), Cop("-->", Name("B"), Name("x"))]), Cop("-->", Name("Q"), Name("c"))),
                Cop("-->", Name("B"), Name("x"))
            ];

            for (iUnittestPremise in unittestPremises) {
                reasoner.inputTerm(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("< < A --> x > ==> < Q --> c > >. {1 0.81}", null) == -1) {
                throw "Unittest failed!";
            }

        }

        { // unittest ==> single premise impl detach
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // <<B --> x> ==> <Q --> c>>.
            // <B --> x>.
            // |-
            // <Q --> c>.
            var unittestPremises:Array<Term> = [
                Cop("==>", Cop("-->", Name("B"), Name("x")), Cop("-->", Name("Q"), Name("c"))),
                Cop("-->", Name("B"), Name("x"))
            ];

            for (iUnittestPremise in unittestPremises) {
                reasoner.inputTerm(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process(40); // needs some more cycles

            if (reasoner.conclusionStrArr.indexOf("< Q --> c >. {1 0.81}", null) == -1) {
                throw "Unittest failed!";
            }

        }

        { // unittest <=> single premise impl detach
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // <<B --> x> <=> <Q --> c>>.
            // <B --> x>.
            // |-
            // <Q --> c>.
            var unittestPremises:Array<Term> = [
                Cop("<=>", Cop("-->", Name("B"), Name("x")), Cop("-->", Name("Q"), Name("c"))),
                Cop("-->", Name("B"), Name("x"))
            ];

            for (iUnittestPremise in unittestPremises) {
                reasoner.inputTerm(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("< Q --> c >. {1 0.81}", null) == -1) {
                throw "Unittest failed!";
            }

        }
        
        { // unittest ==> two premise impl structural transformation
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            reasoner.input("<<$x-->d> ==> <$x-->e>>.");
            reasoner.input("<c-->d>.");
            // |-
            // <c-->e>. [1]

            reasoner.process(140); // needs some more cycles

            if (reasoner.conclusionStrArr.indexOf("< c --> e >. {1 0.81}", null) == -1) {
                throw "Unittest failed!";
            }
        }

        { // unittest <=> two premise impl structural transformation
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            reasoner.input("<<$x-->d> <=> <$x-->e>>.");
            reasoner.input("<c-->d>.");
            // |-
            // <c-->e>. [1]

            reasoner.process(240); // needs some more cycles

            if (reasoner.conclusionStrArr.indexOf("< c --> e >. {1 0.81}", null) == -1) {
                throw "Unittest failed!";
            }
        }



        { // unittest Q&A 
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            reasoner.input("<B --> x>?");
            reasoner.input("<B --> x>.");
            // has to get answered

            reasoner.process(20);

            if (reasoner.conclusionStrArr.indexOf("Answer:[  ?ms]< B --> x >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }

        }

        { // unittest Q&A with var
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            reasoner.input("<?B --> x>?");
            reasoner.input("<B --> x>.");
            // has to get answered

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("Answer:[  ?ms]< B --> x >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }

        }

        { // unittest structural <->
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            reasoner.input("<B <-> x>.");
            
            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("< x <-> B >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }
        }

        { // unittest structural <=>
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            reasoner.input("<B <=> x>.");
            

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("< x <=> B >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }
        }





        /* commented because BS
        { // unittest ==> detachment with swizzled premise 
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // (&&, <A --> x>, <B --> y>) ==> <Q --> c>.
            // (&&, <B --> y>, <A --> x>).
            // |-
            // <Q --> c>.
            var unittestPremises:Array<Term> = [
                Cop("==>", Compound("&&", [Cop("-->", Name("A"), Name("x")), Cop("-->", Name("B"), Name("y"))]), Cop("-->", Name("Q"), Name("c"))),
                Compound("&&", [Cop("-->", Name("B"), Name("y")), Cop("-->", Name("A"), Name("x"))])
            ];

            for (iUnittestPremise in unittestPremises) {
                reasoner.inputTerm(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process();

            // test for output must contain "< Q --> c >. {1 0.81}"
            if (reasoner.conclusionStrArr.indexOf("< Q --> c >. {1 0.81}", null) == -1) {
                throw "Unittest failed!";
            }

        } */



        ProtoLexer.main(); // test parser

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

    // puts judgment into corresponding concepts
    public function updateConceptsForJudgment(sentence:Sentence) {
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

class WorkingSetEntity {
    public var sentence:Sentence;

    public var bestAnswerExp:Float = 0.0;

    public var accuScore = 0.0; // accumulated score of the items in working set up to this item, we store it here for efficiency

    public function new(sentence) {
        this.sentence = sentence;
    }

    public function calcUtility() {
        if (sentence.punctation == "?") {
            // TODO< take time into account >
            // questions don't have a TV so we have to provide a specific base utility
            return 0.8; // TODO< expose as tunable parameter >
        }
        
        // TODO< take time into account >
        return sentence.tv.conf;
    }
}


class WorkingSet {
    public var entities:Array<WorkingSetEntity> = [];

    public function new() {}

    // append, maintains invariants
    public function append(entity:WorkingSetEntity) {
        entities.push(entity);

        if (entities.length >= 2) {
            entities[entities.length-1].accuScore = entities[entities.length-2].accuScore;
        }

        entities[entities.length-1].accuScore += entity.calcUtility();
    }

    public function debug() {
        for (iEntity in entities) {
            trace('   ${TermUtils.convToStr(iEntity.sentence.term)}${iEntity.sentence.punctation}  score=${iEntity.calcUtility()}');
        }        
    }

    // commented because not used
    //public function sort() {
    //    entities.sort(function (a, b) {
    //        if (a.calcUtility() > b.calcUtility()) {
    //            return 1;
    //        }
    //        else if (a.calcUtility() == b.calcUtility()) {
    //            return 0;
    //        }
    //        return -1;
    //    });
    //}

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

    /* commented because not used
    // inserts a Task back into the entities list
    // it assumes that entities is sorted!
    public function insertSorted(entity:WorkingSetEntity, depth=0, minIdx=0, maxIdx=null) {
        if (entities.length == 0) {
            entities = [entity];
            return;
        }
        
        if (maxIdx == null) {
            maxIdx = entities.length-1;
        }

        var insertedUtility = entity.calcUtility();

        var minUtility = entities[minIdx].calcUtility();
        var maxUtility = entities[maxIdx].calcUtility();


        //if (depth > 5) {
        //    throw "DEBUG ERROR";
        //}
        //
        trace('l=${entities.length}');
        trace('insertSorted minIdx=$minIdx maxIdx=$maxIdx');

        if (minIdx == maxIdx - 1 || minIdx == maxIdx) {
                trace("BEFORE");

                for (iEntity in entities) {
                    trace('   ${TermUtils.convToStr(iEntity.sentence.term)}${iEntity.sentence.punctation}  score=${iEntity.calcUtility()}');
                }

            
            // we need to insert here
            //if (entities[minIdx].calcUtility())
            
            if (insertedUtility < maxUtility) {
                entities.insert(maxIdx+1, entity);
            }
            else if (insertedUtility < minUtility) {
                entities.insert(maxIdx, entity);
            }
            else {
                entities.insert(minIdx, entity);
            }
            
            

            trace("AFTER");

                for (iEntity in entities) {
                    trace('   ${TermUtils.convToStr(iEntity.sentence.term)}${iEntity.sentence.punctation}  score=${iEntity.calcUtility()}');
                }


            // check if order is correct
            {
                var idx = 0;
                while (idx < entities.length-1) {
                    if (entities[idx].calcUtility() < entities[idx+1].calcUtility()) {
                        throw "Validation failed!";
                    }
                    idx+=1;
                }
            }
            
        
            

            return;
        }


        // we use binary sort

        var midIdx = Std.int((maxIdx+minIdx) / 2);
        var utilityOfMid = entities[midIdx].calcUtility();

        if (insertedUtility > utilityOfMid) {
            insertSorted(entity, depth+1, minIdx, midIdx);
        }
        else {
            insertSorted(entity, depth+1, midIdx, maxIdx);
        }
    }
    */
}

class Config {
    public static var beliefsPerNode:Int = 30;
    public static var debug_derivations:Bool = false; // debug derivations to console
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
            case Set(_,_):
            return false; // doesn't unify because not equal
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

// commented because not used but it is in here because it may be useful someday
/*
class Utils {
    @:generic public static function arrRemoveAt<T>(arr:Array<T>, idx:Int):Array<T> {
        var before = arr.slice(0, idx);
        var after = arr.slice(idx+1, arr.length);
        return before.concat(after);
    }
    /+
    public static function main() {
        trace(arrRemoveAt([0], 0));
        trace("---");
        trace(arrRemoveAt([0, 1], 0));
        trace(arrRemoveAt([0, 1], 1));
        trace("---");
        trace(arrRemoveAt([0, 1, 2], 0));
        trace(arrRemoveAt([0, 1, 2], 1));
        trace(arrRemoveAt([0, 1, 2], 2));
    }
    +/
}
*/









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
                "PROD";
                case _:
                throw "Parsing failed: content in \"(\" ... \")\" must be a product!"; // TODO< can also be a image >
            }

            switch (type) {
                case "PROD": // is a product

                if (braceContent.length%2 != 1) { // must be uneven
                    throw "Parsing failed: invalid product!";
                }

                // check type
                var idx = 1;
                while (idx < braceContent.length) {
                    switch (braceContent[idx]) {
                        case Name("*"):
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
                        case Name("*"):
                        throw "Parsing failed: product elements must not be * !";
                        case _:
                        productContent.push(braceContent[idx]);
                    }
                    idx+=2;
                }

                // build and return Prod(productContent) to stack
                parser2.stack.push(Prod(productContent));

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
            // TODO
        }

        function bracketSetEnd(parser : Parser<EnumOperationType>, currentToken : Token<EnumOperationType>) {
            var parser2 = cast(parser, NarseseParser);
            // TODO
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
            /*  31 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 12, null, 32, 33), // "{"
            /*  32 */new Arc<EnumOperationType>(EnumArcType.ARC, 80, null, 0, null),
            /*  33 */new Arc<EnumOperationType>(EnumArcType.OPERATION, 14, null, 34, null), // "["
            /*  34 */new Arc<EnumOperationType>(EnumArcType.ARC, 90, null, 0, null),

            /*  35 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  36 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
            /*  37 */new Arc<EnumOperationType>(EnumArcType.ERROR, 0, null, -1, null),
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


// TODO< add support for sets in language >
// TODO< add support for sets to parser (I just need to write the function which is called to create a set) >
// TODO< test sets parsing >

// TODO< add tv to parsing >
// TODO< add event occurence to parser >
