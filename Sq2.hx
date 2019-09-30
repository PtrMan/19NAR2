// run with
//    haxe --interp -main Sq2.hx



// TODO< most NAL-2 like in new meta rules >

// todo< equivalence structural transformation with two premises ded >
// TODO< impl structural transformation with two premises ded >

// TODO< structural transform from images back to products >
// TODO TEST< structural transform from images back to products >
// TODO TEST< structural transform from products to images >


// TODO< attention mechanism : sort after epoch and limit size for next epoch >

// TODO< test attention mechanism with A-->I example from ALANN >

// TODO< revision >

// TODO< attention mechansim : questions have way higher priority than judgments >

// TODO< attention mechanism : stresstest attention >

// TODO< keep concepts under AIKR (ask patrick how)>

// TODO< add sets >

// TODO COMPLICATED< Q&A - do structural transformations on question side without adding the question to the memory or the tasks, sample all possible structural transformations and remember which transformations were done, etc >

// DONE< variables >

// DONE< structural transformation of <-> and <=> >
// DONE TEST< unittest structural transformation of <-> and <=> >


// TODO< rename to Node like in ALANN >
class Concept {
    public var name:Term; // name of the concept

    public var judgments: Array<Sentence> = []; // all judgments of the concept

    public function new(name) {
        this.name = name;
    }
}

class Memory {
    // name key is name as string
    public var conceptsByName:Map<String, Concept> = new Map<String, Concept>();

    public function new() {}

    public function hasConceptByName(name:String) {
        return conceptsByName.get(name) != null;
    }

    public function retConceptByName(name:String): Concept {
        return conceptsByName.get(name);
    }

    public function addConcept(concept:Concept) {
        conceptsByName.set( TermUtils.convToStr(concept.name) , concept);
    }

    // puts judgment into corresponding concepts
    public function updateConceptsForJudgment(sentence:Sentence) {
        for (iTermName in TermUtils.enumTerms(sentence.term)) {
            var conceptOfTerm;
            
            // retrieve or create concept
            if (hasConceptByName(TermUtils.convToStr(iTermName))) {
                conceptOfTerm = retConceptByName(TermUtils.convToStr(iTermName));
            }
            else {
                conceptOfTerm = new Concept(iTermName);
                addConcept(conceptOfTerm);
            }

            // we need to check for the existence of a judgment with the same stamp and TV
            var exists = false;
            for (iJudgment in conceptOfTerm.judgments) {
                if (Sentence.equal(iJudgment, sentence)) {
                    exists = true;
                    break;
                }
            }

            if (exists) {
                continue;
            }

            // update
            conceptOfTerm.judgments.push(sentence);

            // TODO< sort judgments by metric >
        }
    }
}

class StructuralOriginsStamp {
    public var arr:Array<Term> = [];

    public function new(arr) {
        this.arr = arr;
    }

    public static function equal(a:StructuralOriginsStamp, b:StructuralOriginsStamp):Bool {
        if (a.arr.length != b.arr.length) {
            return false;
        }

        for (idx in 0...a.arr.length) {
            if (!TermUtils.equal(a.arr[idx], b.arr[idx])) {
                return false;
            }
        }

        return true;
    }

    public static function checkOverlap(a:StructuralOriginsStamp, b:StructuralOriginsStamp):Bool {
        if (a.arr.length == 0 && b.arr.length == 0) {
            return false; // false because it is a special case because both structural stamps are empty
        }
        return StructuralOriginsStamp.equal(a, b);
    }
}

class Stamp {
    // we store the structural origin to avoid doing the same conversion over and over again
    public var structuralOrigins:StructuralOriginsStamp;

    public var ids:Array<haxe.Int64>;

    public function new(ids, structuralOrigins) {
        this.ids = ids;
        this.structuralOrigins = structuralOrigins;
    }

    public static function merge(a:Stamp, b:Stamp): Stamp {
        var ids:Array<haxe.Int64> = [];

        var commonIdx = Utils.min(a.ids.length, b.ids.length);
        for (idx in 0...commonIdx) {
            ids.push(a.ids[idx]);
            ids.push(b.ids[idx]);
        }

        if (a.ids.length > b.ids.length) {
            ids = ids.concat(a.ids.slice(commonIdx, a.ids.length));
        }
        else if (b.ids.length > a.ids.length) {
            ids = ids.concat(b.ids.slice(commonIdx, b.ids.length));
        }

        // limit size of stamp
        var maxStampLength = 2000;
        ids = ids.slice(0, Utils.min(maxStampLength, ids.length));

        return new Stamp(ids, new StructuralOriginsStamp([])); // throw structural orgin of parameters away because a merge invalidates it anyways
    }

    public static function checkOverlap(a:Stamp, b:Stamp, checkStructural=true):Bool {
        // check normal stamp
        for (iA in a.ids) {

            // TODO< speedup with hashmap >
            for (iB in b.ids) {
                if (haxe.Int64.compare(iA, iB) == 0) {
                    return true;
                }
            }
        }

        if (!checkStructural) {
            return false;
        }

        if (checkStructural && !StructuralOriginsStamp.checkOverlap(a.structuralOrigins, b.structuralOrigins)) {
            return false;
        }
        return true;
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

    public function new(sentence) {
        this.sentence = sentence;
    }

    public function calcUtility() {
        // TODO< take time into account >
        return sentence.tv.conf;
    }
}


class WorkingSet {
    public var entities:Array<WorkingSetEntity> = [];

    public function new() {}

    public function sort() {
        entities.sort(function (a, b) {
            if (a.calcUtility() > b.calcUtility()) {
                return 1;
            }
            else if (a.calcUtility() == b.calcUtility()) {
                return 0;
            }
            return -1;
        });
    }
}


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
    public function input(term:Term, tv:Tv, punctation:String) {
        var sentence = new Sentence(term, tv, new Stamp([stampIdCounter.copy()], new StructuralOriginsStamp([])), punctation);
        stampIdCounter = haxe.Int64.add(stampIdCounter, haxe.Int64.make(0,1));

        if (punctation == ".") { // only add to memory for judgments
            mem.updateConceptsForJudgment(sentence);
        }

        var workingSetEntity = new WorkingSetEntity(sentence);

        workingSet.entities.push(workingSetEntity);
    }

    // run the reasoner for a number of cycles
    public function process() {
        function reportAnswer(sentence:Sentence) {
            var str = 'Answer:[  ?ms]${sentence.convToStr()}'; // report with ALANN formalism

            if (conclusionStrArr != null) { // used for debugging and unittesting
                conclusionStrArr.push(str);
            }

            trace(str);
        }

        var cycleCounter = -1;
        while(true) { // main loop
            cycleCounter++;

            if (cycleCounter > 20) {
                break;
            }

            trace("");
            trace("");
            trace("");

            // select random element from working set
            var idx:Int = Std.random(workingSet.entities.length);
            var chosenWorkingSetEntity = workingSet.entities[idx];

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
                    var conceptOfTerm: Concept = mem.retConceptByName(TermUtils.convToStr(iTermName));

                    // try to find better answer
                    for (iBelief in conceptOfTerm.judgments) {
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
                    trace("two premise derivation !");

                    var secondaryIdx = Std.random(primaryConcept.judgments.length);
                    var secondarySentence = primaryConcept.judgments[secondaryIdx];

                    var secondaryTerm = secondarySentence.term;
                    var secondaryTv = secondarySentence.tv;
                    var secondaryPunctation = secondarySentence.punctation;
                    var secondaryStamp = secondarySentence.stamp;

                    trace("inf   " +  TermUtils.convToStr(premiseTerm) +     "   ++++    "+TermUtils.convToStr(secondaryTerm));

                    if (!Stamp.checkOverlap(premiseStamp, secondaryStamp)) {
                        

                        var conclusionsTwoPremisesAB = deriveTwoPremise(premiseTerm, premiseTv, premisePunctation, premiseStamp,   secondaryTerm, secondaryTv, secondaryPunctation, secondaryStamp);
                        var conclusionsTwoPremisesBA = deriveTwoPremise(secondaryTerm, secondaryTv, secondaryPunctation, secondaryStamp,   premiseTerm, premiseTv, premisePunctation, premiseStamp);
                        conclusionsTwoPremises = [].concat(conclusionsTwoPremisesAB).concat(conclusionsTwoPremisesBA);
                    }
                    else {
                        trace('   stampOverlap a=${premiseStamp.ids.map(v -> haxe.Int64.toStr(v))}  b=${secondaryStamp.ids.map(v -> haxe.Int64.toStr(v))}');
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

            trace("|-");
            for (iConclusion in conclusions) {
                var conclusionAsStr = TermUtils.convToStr(iConclusion.term) +  iConclusion.punctation+" " + iConclusion.tv.convToStr();
                trace(conclusionAsStr);

                if (conclusionStrArr != null) { // used for debugging and unittesting
                    conclusionStrArr.push(conclusionAsStr);
                }
            }



            trace("");
            trace("");
            trace("");


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
                    workingSet.entities.push(workingSetEntity);
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

        trace("Summary: ");
        trace('   #concepts= $numberOfConcepts');
        trace('   #workingset.entities= ${workingSet.entities.length}');


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
                    case Compound(foldedType,content):
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
                            var conclusionTerm = Cop(copAsym, a0, c);
                            conclusions.push({term:conclusionTerm, tv:Tv.deduction(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-2.two ded"});
                            
                            case Cop(copAsymZ0, c, b1) if (copAsymZ0 == copAsym && TermUtils.equal(b0,b1)):

                            // print ("(A "+copAsym+" B),\t(C "+copAsymZ+" B)\t\t\t|-\t(A "+copAsym+" C)\t\t(Truth:Induction"+IntervalProjection+OmitForHOL(", Desire:Weak")+")")
                            var conclusionTerm = Cop(copAsym, a0, c);
                            conclusions.push({term:conclusionTerm, tv:Tv.induction(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-2.two ind"});
                            
                            case Cop(copAsymZ0, a1, c) if (copAsymZ0 == copAsym && TermUtils.equal(a0,a1)):

                            // print ("(A "+copAsym+" B),\t(A "+copAsymZ+" C)\t\t\t|-\t(B "+copAsym+" C)\t\t(Truth:Abduction"+IntervalProjection+OmitForHOL(", Desire:Strong")+")")
                            var conclusionTerm = Cop(copAsym, a0, c);
                            conclusions.push({term:conclusionTerm, tv:Tv.abduction(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-2.two abd"});

                            case _:null;

                        }

                        if (copSym != null) {
                            var copSymZ = copSym; //.replace("t","z");

                            switch (premiseBTerm) {                                
                                case Cop(copSymZ0, c, b1) if (copSymZ0 == copSym && TermUtils.equal(b0,b1)):

                                //print ("(A "+copAsym+" B),\t(C "+copSymZ+" B)\t\t\t|-\t(A "+copAsym+" C)\t\t(Truth:Analogy"+IntervalProjection+OmitForHOL(", Desire:Strong")+")")
                                var conclusionTerm = Cop(copAsym, a0, c);
                                conclusions.push({term:conclusionTerm, tv:Tv.analogy(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-2.two ana1"});

                                case Cop(copSymZ0, c, a1) if (copSymZ0 == copSym && TermUtils.equal(a0,a1)):

                                //print ("(A "+copAsym+" B),\t(C "+copSymZ+" A)\t\t\t|-\t(C "+ival(copSym,"t+z")+" B)\t\t(Truth:Analogy"+OmitForHOL(", Desire:Strong")+")")
                                var conclusionTerm = Cop(copSym, c, b0);
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
                                var conclusionTerm = Cop(copSym, a0, c);
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
                        var conclusionTerm = Cop("-->", conclusionSubj, predA);
                        conclusions.push({term:conclusionTerm, tv:Tv.union(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-3.two union"});
                    }

                    {
                        // #R[(P --> M) (S --> M) |- ((S | P) --> M) :post (:t/intersection)
                        var conclusionSubj = fold("|", Compound("|",[subjA, subjB]));
                        var conclusionTerm = Cop("-->", conclusionSubj, predA);
                        conclusions.push({term:conclusionTerm, tv:Tv.intersection(premiseATv, premiseBTv), punctation:".", stamp:mergedStamp, ruleName:"NAL-3.two intersection"});
                    }


                    case _: null;
                }

                case _: null;
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
                    var conclusion = Cop("==>", compoundA1, implPred);
                    conclusions.push({term: conclusion, tv:Tv.deduction(premiseATv, premiseBTv)/*TODO check*/, punctation:".", stamp:mergedStamp, ruleName:"NAL6-two impl ==> detach conj[0]"});
                }

                // TODO< var unification >
                // ex:
                // <(&&,<a --> x>,<c --> x>) ==> <X --> Y>>.
                // <c-->x>.
                // |-
                // <a --> x> ==> <X --> Y>.
                if (TermUtils.equal(compoundA1, premiseBTerm)) {
                    var conclusion = Cop("==>", compoundA0, implPred);
                    conclusions.push({term: conclusion, tv:Tv.deduction(premiseATv, premiseBTv)/*TODO check*/, punctation:".", stamp:mergedStamp, ruleName:"NAL6-two impl ==> detach conj[1]"});
                }

                case Cop("==>", implSubj, implPred):
                // TODO< var unification >
                // ex:
                // <a --> x> ==> <X --> Y>>.
                // <a-->x>.
                // |-
                // <X --> Y>.
                if (TermUtils.equal(implSubj, premiseBTerm)) {
                    var conclusion = implPred;
                    conclusions.push({term: conclusion, tv:Tv.deduction(premiseATv, premiseBTv)/*TODO check*/, punctation:".", stamp:mergedStamp, ruleName:"NAL6-two impl ==> detach"});
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
            
            var conclusionTerm = Cop(copula, pred,subj);
            
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
            
            var conclusionTerm = Cop(copula, pred,subj);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                conclusions.push({term:conclusionTerm, tv:premiseTv, punctation:".", stamp:new Stamp(premiseStamp.ids, structuralOrigins), ruleName:(copula == "<->" ? "NAL-2" : "NAL-6") + ".single structural"});
            }

            case _: null;
        }


        // NAL-6  product to image transform
        if (premisePunctation == ".") switch (premiseTerm) {
            case Cop("-->", Prod([prod0, prod1]), inhPred):

            // TODO< bump derivation depth >

            var conclusionTerm = Cop("-->", prod0, Img(inhPred, [ImgWild, prod1]));
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                // <prod0 --> (/,inhPred,_,prod1)>
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                conclusions.push({term:conclusionTerm, tv:premiseTv, punctation:".", stamp:new Stamp(premiseStamp.ids, structuralOrigins), ruleName:"NAL-6.single prod->img"});
            }

            conclusionTerm = Cop("-->", prod1, Img(inhPred, [prod0, ImgWild]));
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions

                // <prod1 --> (/,inhPred,prod0,_)>
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                conclusions.push({term:conclusionTerm, tv:premiseTv, punctation:".", stamp:new Stamp(premiseStamp.ids, structuralOrigins), ruleName:"NAL-6.single prod->img"});
            }

            case _: null;
        }

        // TODO< from image to product >

        trace(TermUtils.convToStr(premiseTerm)+premisePunctation);

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


        /* small test experiment #2
        { // create "seed" premise and put it into working set
            var premiseTerm:Term = Cop("-->", Name("a"), Name("c"));
            var premiseTermStructuralOrigins:Array<Term> = [];
            var premiseTv:Tv = new Tv(1.0, 0.9);

            var sentence = new Sentence(premiseTerm, premiseTv, new Stamp(new StructuralOriginsStamp([])), ".");
            mem.updateConceptsForJudgment(sentence);

            var workingSetEntity = new WorkingSetEntity(sentence);

            workingSet.entities.push(workingSetEntity);
        }

        { // create "seed" premise and put it into working set
            var premiseTerm:Term = Cop("-->", Name("b"), Name("c"));
            var premiseTermStructuralOrigins:Array<Term> = [];
            var premiseTv:Tv = new Tv(1.0, 0.9);

            var sentence = new Sentence(premiseTerm, premiseTv, new Stamp(new StructuralOriginsStamp([])), ".");
            mem.updateConceptsForJudgment(sentence);

            var workingSetEntity = new WorkingSetEntity(sentence);

            workingSet.entities.push(workingSetEntity);
        }

        */







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

        { // unittest ==> detachment 
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // (&&, <A --> x>, <B --> x>) ==> <Q --> c>.
            // <A --> x>.
            // |-
            // <B --> x> ==> <Q --> c>.
            var unittestPremises:Array<Term> = [
                Cop("==>", Compound("&&", [Cop("-->", Name("A"), Name("x")), Cop("-->", Name("B"), Name("x"))]), Cop("-->", Name("Q"), Name("c"))),
                Cop("-->", Name("A"), Name("x"))
            ];

            for (iUnittestPremise in unittestPremises) {
                reasoner.input(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("< < B --> x > ==> < Q --> c > >. {1 0.81}", null) == -1) {
                throw "Unittest failed!";
            }

        }

        { // unittest ==> detachment 
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // (&&, <A --> x>, <B --> x>) ==> <Q --> c>.
            // <B --> x>.
            // |-
            // <A --> x> ==> <Q --> c>.
            var unittestPremises:Array<Term> = [
                Cop("==>", Compound("&&", [Cop("-->", Name("A"), Name("x")), Cop("-->", Name("B"), Name("x"))]), Cop("-->", Name("Q"), Name("c"))),
                Cop("-->", Name("B"), Name("x"))
            ];

            for (iUnittestPremise in unittestPremises) {
                reasoner.input(iUnittestPremise, new Tv(1.0, 0.9), ".");
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
                reasoner.input(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("< Q --> c >. {1 0.81}", null) == -1) {
                throw "Unittest failed!";
            }

        }

        { // unittest Q&A 
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // <B --> x>?
            // <B --> x>.
            // has to get answered
            var unittestPremise = Cop("-->", Name("B"), Name("x"));

            reasoner.input(unittestPremise, null, "?");
            reasoner.input(unittestPremise, new Tv(1.0, 0.9), ".");
            

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("Answer:[  ?ms]< B --> x >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }

        }

        { // unittest Q&A with var
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // <?B --> x>?
            // <B --> x>.
            // has to get answered
            reasoner.input(Cop("-->", Var("?","B"), Name("x")), null, "?");
            reasoner.input(Cop("-->", Name("B"), Name("x")), new Tv(1.0, 0.9), ".");
            

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("Answer:[  ?ms]< B --> x >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }

        }

        { // unittest structural <->
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // <B <-> x>.
            // has to get answered
            var unittestPremise = Cop("<->", Name("B"), Name("x"));
            reasoner.input(unittestPremise, new Tv(1.0, 0.9), ".");
            

            reasoner.process();

            if (reasoner.conclusionStrArr.indexOf("< x <-> B >. {1 0.9}", null) == -1) {
                throw "Unittest failed!";
            }
        }

        { // unittest structural <=>
            var reasoner:Sq2 = new Sq2();
            reasoner.conclusionStrArr = []; // enable output logging

            // <B <=> x>.
            // has to get answered
            var unittestPremise = Cop("<=>", Name("B"), Name("x"));
            reasoner.input(unittestPremise, new Tv(1.0, 0.9), ".");
            

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
                reasoner.input(iUnittestPremise, new Tv(1.0, 0.9), ".");
            }

            reasoner.process();

            // test for output must contain "< Q --> c >. {1 0.81}"
            if (reasoner.conclusionStrArr.indexOf("< Q --> c >. {1 0.81}", null) == -1) {
                throw "Unittest failed!";
            }

        } */

    }
}

enum Term {
    Name(name:String);
    Compound(type:String, content:Array<Term>); // intersection, difference, etc.
    Cop(copula:String, subj:Term, pred:Term); // generalization of anything connected with a copula, for example "-->" "<->" etc.
    Prod(terms:Array<Term>); // product
    Img(base:Term, content:Array<Term>); // image
    ImgWild; // wildcard for image NAL:"_"

    Var(type:String,name:String); // variable, type can be "?","#","$"
}

class TermUtils {
    // clones only the first "level" of a term, used to "break" references to stay under AIKR
    public static function cloneShallow(term:Term):Term {
        return switch (term) {
            case Name(name): Name(name);
            case Compound(type, content): Compound(type, content);
            case Cop(copula, subj, pred): Cop(copula, subj, pred);
            case Prod(content): Prod(content);
            case Img(base, content): Img(base, content); 
            case ImgWild: ImgWild;
            case Var(type,name): Var(type,name);
        }
    }

    // enumerate all concept name terms recursivly
    public static function enumTerms(term:Term):Array<Term> {
        return [term].concat(switch (term) {
            case Name(name): [];
            case Compound(_, content):
            var res = [];
            for (iContent in content) {
                res = res.concat(enumTerms(iContent));
            }
            res;
            case Cop(_, subj, pred): enumTerms(subj).concat(enumTerms(pred));
            case Prod(content):
            var res = [];
            for (iContent in content) {
                res = res.concat(enumTerms(iContent));
            }
            res;
            case Img(base, content):
            var res = [];
            for (iContent in content) {
                res = res.concat(enumTerms(iContent));
            }
            res.push(base);
            res;
            case ImgWild: [];
            case Var(_,_): [];
        });
    }

    // convert to string
    public static function convToStr(term:Term) {
        return switch (term) {
            case ImgWild: "_";
            case Name(name): name;
            case Compound(type,content):
            var narseseContent = content.map(function(i) {return convToStr(i);}).join(' $type ');
            '( $narseseContent )';
            case Cop(copula, subj, pred): '< ${convToStr(subj)} $copula ${convToStr(pred)} >';
            case Img(base, content):
            var narseseContent = content.map(function(i) {return convToStr(i);}).join(" ");
            '(/ ${convToStr(base)} $narseseContent)';
            case Prod(content):
            var narseseContent = content.map(function(i) {return convToStr(i);}).join(" * ");
            '( $narseseContent )';
            case Var(type,name): '$type$name';
        }
    }

    public static function equal(a:Term, b:Term):Bool {
        switch (a) {
            case ImgWild:
            switch(b) {
                case ImgWild:
                return true;
                case _:
                return false;
            }
            case Name(nameA):
            switch(b) {
                case Name(nameB):
                return nameA == nameB;
                case _:
                return false;
            }

            case Compound(typeA, contentA):
            switch(b) {
                case Compound(typeB, contentB):
                if (typeA != typeB) {
                    return false;
                }
                if (contentA.length != contentB.length) { return false; }
                for (idx in 0...contentA.length) {
                    if (!equal(contentA[idx], contentB[idx])) {
                        return false;
                    }
                }
                return true;
                case _:
                return false;
            }

            case Cop(copulaA, subjA, predA):
            switch(b) {
                case Cop(copulaB, subjB, predB):
                if (copulaA != copulaB) { return false; }
                return equal(subjA, subjB) && equal(predA, predB);
                case _:
                return false;
            }
            case Img(baseA, contentA):
            switch(b) {
                case Img(baseB, contentB):
                if (!equal(baseA, baseB)) {
                    return false;
                }
                if (contentA.length != contentB.length) { return false; }
                for (idx in 0...contentA.length) {
                    if (!equal(contentA[idx], contentB[idx])) {
                        return false;
                    }
                }
                return true;
                case _:
                return false;
            }
            case Prod(contentA):
            switch(b) {
                case Prod(contentB):
                if (contentA.length != contentB.length) { return false; }
                for (idx in 0...contentA.length) {
                    if (!equal(contentA[idx], contentB[idx])) {
                        return false;
                    }
                }
                return true;
                case _:
                return false;
            }
            case Var(typeA,nameA):
            switch(b) {
                case Var(typeB,nameB):
                return typeA==typeB && nameA==nameB;
                case _:
                return false;
            }
        }
    }

    public static function isVar(term:Term): Bool {
        return switch (term) {
            case Var(_,_): true;
            case _ : false;
        }
    }
}

class Utils {
    public static function contains(arr:Array<Term>, other:Term):Bool {
        return arr.filter(function(x) {return TermUtils.equal(x, other);}).length > 0;
    }

    public static function min(a:Int, b:Int): Int {
        return a < b ? a : b;
    }
}

class Tv {
    public var conf:Float;
    public var freq:Float;

    public function new(freq, conf) {
        this.freq = freq;
        this.conf = conf;
    }

    public function exp():Float {
        return (freq - 0.5) * conf + 0.5;
    }

    public function convToStr():String {
        return '{$freq $conf}';
    }

    /* commented because not used
    public static function contraposition(tv:Tv): Tv {
        var w = and(1.0 - tv.freq, tv.conf);
        var c = w2c(w);
        return new Tv(0, c);
    }*/

    public static function conversion(tv:Tv) {
        var w = and(tv.freq, tv.conf);
        var c = w2c(w);
        return new Tv(1.0, c);
    }

    public static function deduction(a, b) {
        var f = and(a.freq, b.freq);
        var c = and3(a.conf, b.conf, f);
        return new Tv(f, c);
    }

    public static function induction(a, b) {
        return abduction(b, a);
    }

    public static function abduction(a, b) {
        var w = and3(b.freq, a.conf, b.conf);
        var c = w2c(w);
        return new Tv(a.freq, c);
    }

    public static function resemblance(a, b) {
        var f = and(a.freq, b.freq);
        var c = and3(a.conf, b.conf, or(a.freq, b.freq));
        return new Tv(f, c);
    }

    public static function analogy(a, b) {
        var f = and(a.freq, b.freq);
        var c = and3(a.conf, b.conf, b.freq);
        return new Tv(f, c);
    }




    public static function intersection(a, b) {
        var f = and(a.freq, b.freq);
        var c = and(a.conf, b.conf);
        return new Tv(f, c);
    }

    public static function union(a, b) {
        var f = or(a.freq, b.freq);
        var c = and(a.conf, b.conf);
        return new Tv(f, c);
    }

    static function and(a:Float, b:Float) {
        return a*b;
    }
    static function and3(a:Float, b:Float, c:Float) {
        return a*b*c;
    }
    static function or(a:Float, b:Float) {
        var product = 1.0;
        product *= (1.0 - a);
        product *= (1.0 - b);
        return 1.0 - product;
    }

    static function w2c(w) { 
        var horizon = 1.0;
        return w / (w + horizon);
    }
}

class Unifier {
    // substitute variables with actual variables
    // /param varTypes types of variables, can be any string of the combination "?","#","$"
    public static function substitute(term:Term, unifiedMap:Map<String, Term>, varTypes:String): Term {
        function substituteArr(arr:Array<Term>):Array<Term> {
            return arr.map(term -> substitute(term, unifiedMap, varTypes));
        }
        
        switch (term) {
            case Name(name): return term;
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
            case Name(nameA):
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
