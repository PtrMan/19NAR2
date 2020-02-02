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
