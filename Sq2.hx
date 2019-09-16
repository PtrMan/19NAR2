// run with
//    haxe --interp -main Sq2.hx


// TODO< basic Q&A >

// TODO< most NAL-2 like in patricks code generator >

// TODO< concepts: check if judgment exists already >

// TODO< manage stamp >

// TODO< attention mechanism : sort after epoch and limit size for next epoch >

// TODO< revision >

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
        // TODO< check if it is already in concept >

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

            // update
            // TODO< check for existence of sentence with same stamp and TV >
            conceptOfTerm.judgments.push(sentence);
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
}

class Stamp {
    public var structuralOrigins:StructuralOriginsStamp;

    public function new(structuralOrigins) {
        this.structuralOrigins = structuralOrigins;
    }

    public static function checkOverlap(a:Stamp, b:Stamp, checkStructural=true):Bool {
        // TODO< check normal stamp >

        if (checkStructural && !StructuralOriginsStamp.equal(a.structuralOrigins, b.structuralOrigins)) {
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

    public static function equal(a:Sentence, b:Sentence):Bool {
        var epsilon = 0.00001;
        var isTruthEqual = Math.abs(a.tv.freq-b.tv.freq) < epsilon && Math.abs(a.tv.conf-b.tv.conf) < epsilon;
        var isTermEqual = TermUtils.equal(a.term, b.term);
        return isTruthEqual && isTermEqual && a.punctation == b.punctation && Stamp.checkOverlap(a.stamp, b.stamp);
    }
}

class WorkingSetEntity {
    public var sentence:Sentence;

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
    public static function main() {
        var mem:Memory = new Memory();

        // working set of tasks
        var workingSet:WorkingSet = new WorkingSet();

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

            var premiseTerm = chosenWorkingSetEntity.sentence.term;
            var premiseTermStructuralOrigins = chosenWorkingSetEntity.sentence.stamp.structuralOrigins.arr;
            var premiseTv = chosenWorkingSetEntity.sentence.tv;
            var premisePunctation = chosenWorkingSetEntity.sentence.punctation;
            var conclusionsSinglePremise = deriveSinglePremise(premiseTerm, premiseTermStructuralOrigins, premiseTv, premisePunctation);

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
                if (primaryConcept.judgments.length > 0) {
                    trace("two premise derivation !");

                    var secondaryIdx = Std.random(primaryConcept.judgments.length);
                    var secondarySentence = primaryConcept.judgments[secondaryIdx];

                    var secondaryTerm = secondarySentence.term;
                    var secondaryTv = secondarySentence.tv;
                    var secondaryPunctation = secondarySentence.punctation;

                    trace("   " +  TermUtils.convToStr(premiseTerm) +     "   ++++    "+TermUtils.convToStr(secondaryTerm));

                    var conclusionsTwoPremisesAB = deriveTwoPremise(premiseTerm, premiseTv, premisePunctation,   secondaryTerm, secondaryTv, secondaryPunctation);
                    var conclusionsTwoPremisesBA = deriveTwoPremise(secondaryTerm, secondaryTv, secondaryPunctation,   premiseTerm, premiseTv, premisePunctation);
                    conclusionsTwoPremises = [].concat(conclusionsTwoPremisesAB).concat(conclusionsTwoPremisesBA);
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
                trace(TermUtils.convToStr(iConclusion.term) +  "."+" " + iConclusion.tv.convToStr());
            }

            trace("");
            trace("");
            trace("");


            // put conclusions back into working set
            for (iConclusion in conclusions) {
                var stamp:Stamp = new Stamp(new StructuralOriginsStamp(iConclusion.structuralOrigins));
                var sentence = new Sentence(iConclusion.term, iConclusion.tv, stamp, ".");

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
                var stamp:Stamp = new Stamp(new StructuralOriginsStamp(iConclusion.structuralOrigins));

                var sentence = new Sentence(iConclusion.term, iConclusion.tv, stamp, ".");
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


    }

    public static function deriveTwoPremise(premiseATerm:Term,premiseATv:Tv,premiseAPunctation:String,  premiseBTerm:Term,premiseBTv:Tv,premiseBPunctation:String) {
        
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

        // we store the structural origin to avoid doing the same conversion over and over again
        var conclusions:Array<{term:Term, tv:Tv, structuralOrigins:Array<Term>, ruleName:String}> = [];

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
                    case Cop(copAsym, a0, b0):

                    switch (premiseBTerm) {
                        case Cop(copAsymZ, b1, c) if (TermUtils.equal(b0,b1)):

                        // print ("(A "+copAsym+" B),\t(B "+copAsymZ+" C)\t\t\t|-\t(A "+ival(copAsym,"t+z")+" C)\t\t(Truth:Deduction"+OmitForHOL(", Desire:Strong")+")")
                        var conclusionTerm = Cop(copAsym, a0, c);
                        conclusions.push({term:conclusionTerm, tv:Tv.deduction(premiseATv, premiseBTv), structuralOrigins:[], ruleName:"NAL-2.two ded"});
                        
                        case Cop(copAsymZ, c, b1) if (TermUtils.equal(b0,b1)):

                        // print ("(A "+copAsym+" B),\t(C "+copAsymZ+" B)\t\t\t|-\t(A "+copAsym+" C)\t\t(Truth:Induction"+IntervalProjection+OmitForHOL(", Desire:Weak")+")")
                        var conclusionTerm = Cop(copAsym, a0, c);
                        conclusions.push({term:conclusionTerm, tv:Tv.induction(premiseATv, premiseBTv), structuralOrigins:[], ruleName:"NAL-2.two ind"});
                        
                        case Cop(copAsymZ, a1, c) if (TermUtils.equal(a0,a1)):

                        // print ("(A "+copAsym+" B),\t(A "+copAsymZ+" C)\t\t\t|-\t(B "+copAsym+" C)\t\t(Truth:Abduction"+IntervalProjection+OmitForHOL(", Desire:Strong")+")")
                        var conclusionTerm = Cop(copAsym, a0, c);
                        conclusions.push({term:conclusionTerm, tv:Tv.abduction(premiseATv, premiseBTv), structuralOrigins:[], ruleName:"NAL-2.two abd"});

                        case _:null;

                        case _:null;
                    }

                    case _:null;
                }

                switch (premiseATerm) {
                    case Cop(copAsym, a, b0):

                    switch (premiseBTerm) {
                        case Cop(copAsymZ, c, b1) if (TermUtils.equal(b0,b1)):

                        // print ("(A "+copAsym+" B),\t(B "+copAsymZ+" C)\t\t\t|-\t(A "+ival(copAsym,"t+z")+" C)\t\t(Truth:Deduction"+OmitForHOL(", Desire:Strong")+")")
                        var conclusionTerm = Cop(copAsym, a, c);
                        conclusions.push({term:conclusionTerm, tv:Tv.deduction(premiseATv, premiseBTv), structuralOrigins:[], ruleName:"NAL-2.two ded"});
                        
                        case _:null;
                    }

                    case _:null;
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
                    conclusions.push({term:conclusionTerm, tv:Tv.union(premiseATv, premiseBTv), structuralOrigins:[], ruleName:"NAL-3.two union"});
                }

                {
                    // #R[(P --> M) (S --> M) |- ((S | P) --> M) :post (:t/intersection)
                    var conclusionSubj = fold("|", Compound("|",[subjA, subjB]));
                    var conclusionTerm = Cop("-->", conclusionSubj, predA);
                    conclusions.push({term:conclusionTerm, tv:Tv.intersection(premiseATv, premiseBTv), structuralOrigins:[], ruleName:"NAL-3.two intersection"});
                }


                case _: null;
            }

            case _: null;
        }

        return conclusions;
    }

    // single premise derivation
    public static function deriveSinglePremise(premiseTerm:Term,premiseTermStructuralOrigins:Array<Term>,premiseTv:Tv,premisePunctation:String) {

        // we store the structural origin to avoid doing the same conversion over and over again
        var conclusions:Array<{term:Term, tv:Tv, structuralOrigins:Array<Term>, ruleName:String}> = [];

        // NAL-2 conversion
        switch (premiseTerm) {
            case Cop(copula, subj, pred) if (copula == "-->" || copula == "<->"):

            // TODO< bump derivation depth >
            
            var conclusionTerm = Cop(copula, pred,subj);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                conclusions.push({term:conclusionTerm, tv:Tv.conversion(premiseTv), structuralOrigins:premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]), ruleName:"NAL-2.single contraposition"});
            }

            case _: null;
        }


        // NAL-6  product to image transform
        switch (premiseTerm) {
            case Cop("-->", Prod([prod0, prod1]), inhPred):

            // TODO< bump derivation depth >

            var conclusionTerm = Cop("-->", prod0, Img(inhPred, [ImgWild, prod1]));
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                // <prod0 --> (/,inhPred,_,prod1)>
                conclusions.push({term:conclusionTerm, tv:premiseTv,  structuralOrigins:premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]), ruleName:"NAL-6.single prod->img"});
            }

            conclusionTerm = Cop("-->", prod1, Img(inhPred, [prod0, ImgWild]));
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions

                // <prod1 --> (/,inhPred,prod0,_)>
                conclusions.push({term:conclusionTerm, tv:premiseTv,  structuralOrigins:premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]), ruleName:"NAL-6.single prod->img"});
            }

            case _: null;
        }

        // TODO< from image to product >

        trace(TermUtils.convToStr(premiseTerm)+premisePunctation);

        return conclusions;
        
    }
}

enum Term {
    Name(name:String);
    Compound(type:String, content:Array<Term>); // intersection, difference, etc.
    Cop(copula:String, subj:Term, pred:Term); // generalization of anything connected with a copula, for example "-->" "<->" etc.
    Prod(terms:Array<Term>); // product
    Img(base:Term, content:Array<Term>); // image
    ImgWild; // wildcard for image NAL:"_"
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
            case _: throw "Internal Error";
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
            case _: throw "Internal Error";
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
            case _: throw "Internal Error";
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
            case _: throw "Internal Error";
        }
    }
}

class Utils {
    public static function contains(arr:Array<Term>, other:Term):Bool {
        return arr.filter(function(x) {return TermUtils.equal(x, other);}).length > 0;
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
