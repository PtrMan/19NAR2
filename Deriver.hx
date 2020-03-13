/*
Copyright 2020 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

/*
TODO

* remove superfluous rules to not generate redudantant code

unittest:

test that it doesn't derive if the set constraints are not fullfilled!

*/

import haxe.macro.Expr;

class Deriver {
    public static function main() {
        trace("start");

        
        var x = Term.Cop("-->", Term.Name("a"), Term.Name("b"));
        var y = Term.Cop("-->", Term.Name("b"), Term.Name("c"));

        var conclusions = [];
        inferenceCode(x, ".", new Tv(1.0, 0.9), y, ".", new Tv(1.0, 0.9), null, conclusions, 1);
        trace(conclusions);
    }

    // macro to compile a lot of rules
    public static macro function inferenceCode(a:Expr, aPunct:Expr, aTv:Expr, b:Expr, bPunct:Expr, bTv:Expr, mergedStamp:Expr, conclusions:Expr, conclDepth:Expr) {
        var cgrules:Array<CGRule> = []; // all code generation rules which we generated
        
        // add set rules
        // <c-->[a]>.
        // <c-->[b]>.
        // |-
        // <c-->[b a]>.
        cgrules.push(new CGRule("-->", "subj", ".",  "-->", "subj", ".",    "a.subj", "-->", "x", [Precond.NotSet("a.subj"), Precond.SetInt("a.pred"), Precond.SetInt("b.pred")], [Postcond.SetUnion("x", "a.pred", "b.pred")], "intersection"));

        // <{a}-->c>.
        // <{b}-->c>.
        // |-
        // <{b a}-->c>.
        cgrules.push(new CGRule("-->", "pred", ".",  "-->", "pred", ".",    "x", "-->", "a.pred", [Precond.NotSet("a.pred"), Precond.SetExt("a.subj"), Precond.SetExt("b.subj")], [Postcond.SetUnion("x", "a.subj", "b.subj")], "intersection"));


        // <P --> M>
        // <S --> M>
        // |-
        // <(S | P) --> M>
        // <(S & P) --> M>
        cgrules.push(new CGRule("-->", "pred", ".",  "-->", "pred", ".",   "x", "-->", "a.pred", [], [Postcond.FoldCompound("x", "|", "a.subj", "b.subj")], "intersection"));
        cgrules.push(new CGRule("-->", "pred", ".",  "-->", "pred", ".",   "x", "-->", "a.pred", [], [Postcond.FoldCompound("x", "&", "a.subj", "b.subj")], "union"));

        // <M --> P>, <M --> S>
        // |-
        // <M --> (P & S)>
        // <M --> (P | S)>
        // <M --> (P - S)>
        cgrules.push(new CGRule("-->", "subj", ".",  "-->", "subj", ".",   "a.subj", "-->", "x", [], [Postcond.FoldCompound("x", "&", "a.pred", "b.pred")], "intersection"));
        cgrules.push(new CGRule("-->", "subj", ".",  "-->", "subj", ".",   "a.subj", "-->", "x", [], [Postcond.FoldCompound("x", "|", "a.pred", "b.pred")], "union"));
        cgrules.push(new CGRule("-->", "subj", ".",  "-->", "subj", ".",   "a.subj", "-->", "x", [], [Postcond.FoldCompound("x", "-", "a.pred", "b.pred")], "difference"));


        // ======
        // generate rules for compact rule-table sylogistic inference for NAL-2 and NAL-6
        for(aCop in ["-->", "<->", "==>", "<=>"]) { // iterate over all copulas the generate code for
            for(bCop in ["-->", "<->", "==>", "<=>"]) { // iterate over all copulas the generate code for
                var aTypeAndNal = switch(aCop) { // dispatch type and nal level of term
                    case "-->": {type:"ASYM",nal:2};
                    case "<->": {type:"SYM",nal:2}; 
                    case "==>": {type:"ASYM",nal:6};
                    case "<=>": {type:"SYM",nal:6}; 
                    case _: null;
                };

                var bTypeAndNal = switch(bCop) { // dispatch type and nal level of term
                    case "-->": {type:"ASYM",nal:2};
                    case "<->": {type:"SYM",nal:2}; 
                    case "==>": {type:"ASYM",nal:6};
                    case "<=>": {type:"SYM",nal:6}; 
                    case _: null;
                };
    

                if (aTypeAndNal != null && bTypeAndNal != null && aTypeAndNal.nal == bTypeAndNal.nal) { // can only do inference when NAL-levels match
                    var nal:Int = aTypeAndNal.nal; // because nal is the same
                    
                    { // same subject   a ??> b    a ??> c  |-   b ??> c
                        var tfn: String = switch({a:aTypeAndNal.type,b:bTypeAndNal.type}) {
                            case {a:"ASYM",b:"ASYM"}: "abduction";
                            case {a:"ASYM",b:"SYM"} | {a:"SYM",b:"ASYM"}: "analogy";
                            case {a:"SYM",b:"SYM"}: "resemblance";
                            case _: throw "Internal error"; // must never happen, is bug when happens
                        };
    
                        var conclCop: String = switch (nal) {
                            case 2: "<->";
                            case 6: "<=>";
                            case _: throw "Internal error";
                        };
    
                        cgrules.push(new CGRule(aCop, "subj", ".",  bCop, "subj", ".",    "a.pred", conclCop, "b.pred", [Precond.NotSet("a.pred"), Precond.NotSet("b.pred")], [], tfn));
                    }

                    { // same predicate   b ??> a   c ??> a  |-   b ??> c
                        var tfn: String = switch({a:aTypeAndNal.type,b:bTypeAndNal.type}) {
                            case {a:"ASYM",b:"ASYM"}: "induction";
                            case {a:"ASYM",b:"SYM"} | {a:"SYM",b:"ASYM"}: "analogy";
                            case {a:"SYM",b:"SYM"}: "resemblance";
                            case _: throw "Internal error"; // must never happen, is bug when happens
                        };
    
                        var conclCop: String = switch (nal) {
                            case 2: "<->";
                            case 6: "<=>";
                            case _: throw "Internal error";
                        };
    
                        cgrules.push(new CGRule(aCop, "pred", ".",    bCop, "pred", ".",     "a.subj", conclCop, "b.subj", [Precond.NotSet("a.subj"), Precond.NotSet("b.subj")], [], tfn));
                    }

                    { // same pred-subj   a ??> b   b ??> c   |-  a ??> c
                        var tfn: String = switch({a:aTypeAndNal.type,b:bTypeAndNal.type}) {
                            case {a:"ASYM",b:"ASYM"} | {a:"ASYM",b:"SYM"} | {a:"SYM",b:"ASYM"}: "deduction";
                            case {a:"SYM",b:"SYM"}: "resemblance";
                            case _: throw "Internal error"; // must never happen, is bug when happens
                        };
    
                        // compute copula for "less sym" result
                        var conclCop = switch(nal) {
                            case 2: (aCop == "<->" || bCop == "<->") ? "<->" : "-->";
                            case 6: (aCop == "<=>" || bCop == "<=>") ? "<=>" : "==>";
                            case _: throw "Internal error";
                        }

                        cgrules.push(new CGRule(aCop, "pred",".",    bCop,"subj",".",     "a.subj", conclCop, "b.pred", [Precond.NotSameSetType("a.subj", "b.pred")], [], tfn));
                    }
                }
            }
        }
        
        var e:Array<Expr> = [];
    
        for(iCGRule in cgrules) { // iterate over all rules
            e.push(
                macro switch($a) {
                    case Term.Cop(copA, subjA, predA) if (copA == $v{iCGRule.aCop}):
                    
                    switch($b) {
                        case Term.Cop(copB, subjB, predB) if (copB == $v{iCGRule.bCop}):
                        
                        if ($aPunct == $v{iCGRule.aPunct} && $bPunct == $v{iCGRule.bPunct}) {
                            // compare syllogistically
                            var aSyl:Term = $v{iCGRule.aCode == "subj"} ? subjA : predA;
                            var bSyl:Term = $v{iCGRule.bCode == "subj"} ? subjB : predB;

                            if (TermUtils.equal(aSyl, bSyl)
                                //&& !TermUtils.isSet(aSyl) // never allow the common term to be a set!
                            ) {
                                var precondsFullfilled = true; // are all preconditions fullfilled?

                                for (iPrecond in $v{iCGRule.preconds}) { // iterate over each precondition
                                    switch (iPrecond) {
                                        case Deriver.Precond.NotSameSetType(a, b):
                                        {
                                            var aTerm: Term = switch(a) {
                                                case "a.subj": subjA;
                                                case "a.pred": predA;
                                                case "b.subj": subjB;
                                                case "b.pred": predB;
                                                case _:null;
                                            }

                                            var bTerm: Term = switch(b) {
                                                case "a.subj": subjA;
                                                case "a.pred": predA;
                                                case "b.subj": subjB;
                                                case "b.pred": predB;
                                                case _:null;
                                            }

                                            if (TermUtils.isSameSet(aTerm, bTerm)) {
                                                precondsFullfilled = false;
                                            }
                                        }

                                        case NotSet(x):
                                        {
                                            var xTerm: Term = switch(x) {
                                                case "a.subj": subjA;
                                                case "a.pred": predA;
                                                case "b.subj": subjB;
                                                case "b.pred": predB;
                                                case _:null;
                                            }

                                            if (TermUtils.isSet(xTerm)) {
                                                precondsFullfilled = false;
                                            }
                                        }

                                        case SetExt(x):
                                        {
                                            var xTerm: Term = switch(x) {
                                                case "a.subj": subjA;
                                                case "a.pred": predA;
                                                case "b.subj": subjB;
                                                case "b.pred": predB;
                                                case _:null;
                                            }

                                            if (!TermUtils.isSetExt(xTerm)) {
                                                precondsFullfilled = false;
                                            }
                                        }

                                        case SetInt(x):
                                        {
                                            var xTerm: Term = switch(x) {
                                                case "a.subj": subjA;
                                                case "a.pred": predA;
                                                case "b.subj": subjB;
                                                case "b.pred": predB;
                                                case _:null;
                                            }

                                            if (!TermUtils.isSetInt(xTerm)) {
                                                precondsFullfilled = false;
                                            }
                                        }
                                    }
                                }
                                
                                if (precondsFullfilled) { // preconditions must be fullfilled
                                    var termX:Term = null; // special term computed by postcondition
                                    
                                    // compute postconditions
                                    for (iPostcond in $v{iCGRule.postconds}) {
                                        
                                        switch(iPostcond) {
                                            
                                            case Deriver.Postcond.SetUnion(dest, a, b): // compute set union
                                            {
                                                var aTerm: Term = switch(a) {
                                                    case "a.subj": subjA;
                                                    case "a.pred": predA;
                                                    case "b.subj": subjB;
                                                    case "b.pred": predB;
                                                    case _:null;
                                                }

                                                var bTerm: Term = switch(b) {
                                                    case "a.subj": subjA;
                                                    case "a.pred": predA;
                                                    case "b.subj": subjB;
                                                    case "b.pred": predB;
                                                    case _:null;
                                                }

                                                // compute actual union
                                                var mergedSet:Term = TermUtils.setMerge2(aTerm, bTerm);

                                                // store
                                                switch (dest) {
                                                    case "x": termX = mergedSet;
                                                    case _:null; // ignore
                                                }
                                            }

                                            case Deriver.Postcond.FoldCompound(dest, type, a, b):
                                            {
                                                var aTerm: Term = switch(a) {
                                                    case "a.subj": subjA;
                                                    case "a.pred": predA;
                                                    case "b.subj": subjB;
                                                    case "b.pred": predB;
                                                    case _:null;
                                                }

                                                var bTerm: Term = switch(b) {
                                                    case "a.subj": subjA;
                                                    case "a.pred": predA;
                                                    case "b.subj": subjB;
                                                    case "b.pred": predB;
                                                    case _:null;
                                                }
                                                
                                                var compound = Term.Compound(type, [aTerm, bTerm]);
                                                compound = TermUtils.fold(type, compound);
                                                
                                                // store
                                                switch (dest) {
                                                    case "x": termX = compound;
                                                    case _:null; // ignore
                                                }
                                            }
                                        }
                                        
                                    }

                                    // now we just need to build conclusion and compute TV

                                    // build conclusion term
                                    var conclSubj: Term = switch($v{iCGRule.conclSubj}) {
                                        case "a.subj": subjA;
                                        case "a.pred": predA;
                                        case "b.subj": subjB;
                                        case "b.pred": predB;
                                        case "x": termX;
                                        case _: null;
                                    }
                                    var conclPred: Term = switch($v{iCGRule.conclPred}) {
                                        case "a.subj": subjA;
                                        case "a.pred": predA;
                                        case "b.subj": subjB;
                                        case "b.pred": predB;
                                        case "x": termX;
                                        case _:null;
                                    }
                                    var conclTerm: Term = Term.Cop($v{iCGRule.conclCop}, conclSubj, conclPred);
                                    
                                    var conclusionTv: Tv = switch ($v{iCGRule.tfn}) {
                                        case "induction": Tv.induction($aTv,$bTv);
                                        case "deduction": Tv.deduction($aTv,$bTv);
                                        case "abduction": Tv.abduction($aTv,$bTv);
                                        case "analogy": Tv.analogy($aTv,$bTv);
                                        case "resemblance": Tv.resemblance($aTv,$bTv);
                                        case "intersection": Tv.intersection($aTv,$bTv);
                                        case "union": Tv.union($aTv,$bTv);
                                        case "difference": Tv.difference($aTv,$bTv);
                                        case _:throw "Internal Error";
                                    }
                                    
                                    
                                    // TODO< transfer rulename from rule to conclusions >
                                    conclusions.push({term:conclTerm, tv:conclusionTv, punctation:".", stamp:$mergedStamp, ruleName:"?", depth:$conclDepth});
                                }
                            }

                        }

                        case _:
                    }
                    case _:
                }
            );
    
        }
        return macro $b{e};
    }

    
    // /param conclDepth derivation depth of the conclusion
    public static function deriveTwoPremise(premiseASentence:Nar.Sentence, premiseATask:Nar.Task, premiseBSentence:Nar.Sentence, premiseBTask:Nar.Task, conclDepth:Int,  conclTasks:Array<Nar.Task>) {
        var conclusionsTwoPremisesAB = deriveTwoPremiseInternal(premiseASentence, premiseATask, premiseBSentence, premiseBTask, conclDepth,  conclTasks);
        var conclusionsTwoPremisesBA = deriveTwoPremiseInternal(premiseBSentence, premiseBTask, premiseASentence, premiseATask, conclDepth,  conclTasks);
        return [].concat(conclusionsTwoPremisesAB).concat(conclusionsTwoPremisesBA);
    }


    // internal helper function which processes only one combination of premises (sides are not switched)
    // /param premiseATask can be null if premise is not associated with a task
    // /param premiseBTask can be null if premise is not associated with a task
    public static function deriveTwoPremiseInternal(premiseASentence:Nar.Sentence, premiseATask:Nar.Task, premiseBSentence:Nar.Sentence, premiseBTask:Nar.Task, conclDepth:Int,  conclTasks:Array<Nar.Task>) {
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

            if (!Nar.Unifier.unify(a, b, unifiedMap)) {
                return null;
            }

            // apply variables and return substitution result
            return Nar.Unifier.substitute(a, unifiedMap, varTypes);
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
                if (Nar.Unifier.unify(subj, premiseBTerm, unifiedMap)) { // try to unify the subj of the impl or equiv w/ the other premise                    
                    var conclTerm = Nar.Unifier.substitute(pred, unifiedMap, "$");
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
                if (Nar.Unifier.unify(pred, premiseBTerm, unifiedMap)) { // try to unify the subj of the impl or equiv w/ the other premise                    
                    var conclTerm = Nar.Unifier.substitute(subj, unifiedMap, "$");
                    conclusions.push({term: conclTerm, tv:null, punctation:"?", stamp:premiseBStamp, ruleName:"NAL6-two impl/equiv Q&A 1", depth:conclDepth});
                }

                case _: null;
            }
        }


        return conclusions;
    }

    // single premise derivation
    public static function deriveSinglePremise(premiseTask:Nar.Task, nar:Nar): Array<Nar.Task> {
        var premiseTerm = premiseTask.sentence.term;
        var premiseTermStructuralOrigins = premiseTask.sentence.stamp.structuralOrigins.arr;
        var premiseTv = premiseTask.sentence.tv;
        var premisePunctation = premiseTask.sentence.punctation;
        var premiseStamp = premiseTask.sentence.stamp;

        var conclusionTasks: Array<Nar.Task> = [];

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
            case Term.Cop(copula, subj, pred) if (copula == "<->" || copula == "<=>"):

            var conclusionTerm = Term.Cop(copula, pred,subj);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                
                // ruleName:(copula == "<->" ? "NAL-2" : "NAL-6") + ".single structural"
                var conclusionSentence = new Nar.Sentence(conclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), ".");
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                conclusionTasks.push(new Nar.JudgementTask(conclusionSentence, nar.taskIdCounter++));
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
                var conclusionSentence = new Nar.Sentence(conclusionTerm, Tv.structDeduction(premiseTv), new Stamp(premiseStamp.ids, structuralOrigins), ".");
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                conclusionTasks.push(new Nar.JudgementTask(conclusionSentence, nar.taskIdCounter++));
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
                var conclusionSentence = new Nar.Sentence(conclusionTerm, Tv.structAbduction(premiseTv), new Stamp(premiseStamp.ids, structuralOrigins), ".");
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                conclusionTasks.push(new Nar.JudgementTask(conclusionSentence, nar.taskIdCounter++));
            }

            case _: null;
        }

        // NAL-3 structural decomposition for question for better Q&A
        var derive_decompositionQuestions = false; // disable because not necessary, seems also to make system unreliable
        if (derive_decompositionQuestions && premisePunctation == "?") switch (premiseTerm) {
            // <(a & b) --> c>?
            // |-
            // <a --> c>?
            // <b --> c>?
            case Cop(cop, Compound(compType, compContent), pred) if (compType == "&" || compType == "|"):
            
            var premiseQuestionTask:Nar.QuestionTask = cast(premiseTask, Nar.QuestionTask);

            // were compositional questions ever derived?
            if (premiseQuestionTask.questionCompositionChildrenLinks.length != compContent.length) {
                premiseQuestionTask.questionCompositionChildrenLinks = []; // simplest solution is to flush 

                var componentIdx = 0; // used for linkage
                for(iCompContent in compContent) {

                    var conclusionTerm = Term.Cop(cop, iCompContent, pred);
    
                    // we don't need to check structural stamp, because it is not necessary
                    var structuralOrigins = new StructuralOriginsStamp([]);
    
                    // ruleName:"NAL-3" + '.single structural decompose $compType'
                    var conclusionSentence = new Nar.Sentence(conclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), premisePunctation);
                    conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                    if (premisePunctation == "?") {
                        var link:Nar.QuestionLink = Nar.QuestionLink.ComposeSingle(componentIdx, premiseQuestionTask.id); // we need to link them
                        var derivedQuestionTask = new Nar.QuestionTask(conclusionSentence, link, nar.taskIdCounter++);
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
                var conclusionSentence = new Nar.Sentence(conclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), premisePunctation);
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                if (premisePunctation == "?") {
                    var link:Nar.QuestionLink = Nar.QuestionLink.StructuralSingle(premiseTask.id); // we need to link them
                    conclusionTasks.push(new Nar.QuestionTask(conclusionSentence, link, nar.taskIdCounter++));
                }
                else {
                    conclusionTasks.push(new Nar.JudgementTask(conclusionSentence, nar.taskIdCounter++));
                }
            }

            conclusionTerm = Term.Cop("-->", prod1, Img(inhPred, [prod0, ImgWild]));
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions

                // <prod1 --> (/,inhPred,prod0,_)>
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );

                // ruleName:"NAL-6.single prod->img"
                var conclusionSentence = new Nar.Sentence(conclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), premisePunctation);
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                if (premisePunctation == "?") {
                    var link:Nar.QuestionLink = Nar.QuestionLink.StructuralSingle(premiseTask.id); // we need to link them
                    conclusionTasks.push(new Nar.QuestionTask(conclusionSentence, link, nar.taskIdCounter++));
                }
                else {
                    conclusionTasks.push(new Nar.JudgementTask(conclusionSentence, nar.taskIdCounter++));
                }
            }

            case _: null;
        }

        // NAL-4  image to product transform
        if (premisePunctation == "." || premisePunctation == "?") switch (premiseTerm) {
            case Term.Cop("-->", inhSubj, Term.Img(inhPred, [Term.ImgWild, prod1])):

            var conclusionTerm = Term.Cop("-->", Prod([inhSubj, prod1]), inhPred);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                // <(*, inhSubj, prod1) --> inhPred>
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                
                // ruleName:"NAL-6.single img->prod"
                var conclusionSentence = new Nar.Sentence(conclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), premisePunctation);
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                if (premisePunctation == "?") {
                    var link:Nar.QuestionLink = Nar.QuestionLink.StructuralSingle(premiseTask.id); // we need to link them
                    conclusionTasks.push(new Nar.QuestionTask(conclusionSentence, link, nar.taskIdCounter++));
                }
                else {
                    conclusionTasks.push(new Nar.JudgementTask(conclusionSentence, nar.taskIdCounter++));
                }
            }


            case Cop("-->", inhSubj, Img(inhPred, [prod0, ImgWild])):

            var conclusionTerm = Term.Cop("-->", Prod([prod0, inhSubj]), inhPred);
            
            if (!Utils.contains(premiseTermStructuralOrigins, conclusionTerm)) { // avoid deriving the same structural conclusions
                // <(*, prod0, inhSubj) --> inhPred>
                var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );

                // ruleName:"NAL-6.single img->prod"
                var conclusionSentence = new Nar.Sentence(conclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), premisePunctation);
                conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                if (premisePunctation == "?") {
                    var link:Nar.QuestionLink = Nar.QuestionLink.StructuralSingle(premiseTask.id); // we need to link them
                    conclusionTasks.push(new Nar.QuestionTask(conclusionSentence, link, nar.taskIdCounter++));
                }
                else {
                    conclusionTasks.push(new Nar.JudgementTask(conclusionSentence, nar.taskIdCounter++));
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
            case Term.Cop(cop, Term.Prod([subj0, subj1]),Term.Prod([pred0, pred1])) if (cop == "-->" || cop == "<->"):

            var conclusionTerms = [Term.Cop(cop, subj0, pred0), Term.Cop(cop, subj1, pred1)];
            
            for (iConclusionTerm in conclusionTerms) {
                if (!Utils.contains(premiseTermStructuralOrigins, iConclusionTerm)) { // avoid deriving the same structural conclusions
                    var structuralOrigins = new StructuralOriginsStamp( premiseTermStructuralOrigins.concat([TermUtils.cloneShallow(premiseTerm)]) );
                    
                    // ruleName:"NAL-6.single struct decomposition"
                    var conclusionSentence = new Nar.Sentence(iConclusionTerm, premiseTv, new Stamp(premiseStamp.ids, structuralOrigins), premisePunctation);
                    conclusionSentence.derivationDepth = premiseTask.sentence.derivationDepth+1;
                    conclusionTasks.push(new Nar.JudgementTask(conclusionSentence, nar.taskIdCounter++));
                }
            }

            case _: null;
        }


        if (Nar.Config.debug_derivations)   trace(TermUtils.convToStr(premiseTerm)+premisePunctation);

        return conclusionTasks;
        
    }
}

// syllogistic code gen rule
class CGRule {
    // /param tfn truth-function
    public function new(aCop, aCode, aPunct, bCop, bCode,bPunct,    conclSubj, conclCop, conclPred, preconds:Array<Precond>, postconds:Array<Postcond>, tfn:String) {
        this.aCop=aCop; this.aCode=aCode;
        this.aPunct=aPunct; this.bPunct=bPunct;
        this.bCop=bCop; this.bCode=bCode;
        this.conclSubj=conclSubj;
        this.conclCop=conclCop;
        this.conclPred=conclPred;
        this.preconds=preconds;
        this.postconds=postconds;
        this.tfn=tfn;
    }

    public var aCop:String;
    public var aPunct:String;
    public var aCode:String;
    public var bCop:String;
    public var bPunct:String;
    public var bCode:String;
    public var conclSubj:String;
    public var conclCop:String;
    public var conclPred:String;
    public var preconds:Array<Precond>; // precondition predicates
    public var postconds:Array<Postcond>; // postcondition predicates
    public var tfn:String;
}


// postcondition - used for composing result
enum Postcond {
    SetUnion(dest:String, a:String, b:String); // compute set union and store under variable "dest"
    FoldCompound(dest:String, type:String, a:String, b:String); // create compound, fold it, and store under variable "dest"
}

// precondition
enum Precond {
    NotSameSetType(a:String, b:String); // check that the premises don't have the same set type, set types can be extensional or intensional
    NotSet(a:String);
    SetExt(a:String);
    SetInt(a:String);
}
