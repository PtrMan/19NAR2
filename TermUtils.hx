/*
Copyright 2019 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

class TermUtils {
    // rewrites <-> to <-> and both versions of --> which are "views"
    public static function rewriteSimToSimInhView(term:Term): Array<Term> {
        switch term {
            case Cop("<->", subj,pred):
            return [term, Cop("<->",pred,subj), Cop("-->",subj,pred), Cop("-->",pred,subj)];
            case _:
            return [term];
        }
    }

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
            case Str(content): Str(content);
            case Set(type, content): Set(type, content);
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
            case Str(_): [];

            case Set(_, _):
            [term]; // we treat a set as it's own name 
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
            case Str(content): '"$content"'; // TODO< escape " and \   >
            case Set(type, content):
            var narseseContent = content.map(function(i) {return convToStr(i);}).join(" ");
            var typeEnd = type == "{" ? "}" : "]";
            '$type$narseseContent$typeEnd';
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

            case Str(contentA):
            switch(b) {
                case Str(contentB):
                return contentA==contentB;
                case _:
                return false;
            }

            case Set(typeA,contentA):
            switch(b) {
                case Set(typeB,contentB):
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
        }
    }

    public static function isVar(term:Term): Bool {
        return switch (term) {
            case Var(_,_): true;
            case _ : false;
        }
    }

    
    public static function isSet(term:Term): Bool {
        return switch (term) {
            case Set(_,_): true;
            case _ : false;
        }
    }

    public static function isSetExt(term:Term): Bool {
        return switch (term) {
            case Set("{",_): true;
            case _ : false;
        }
    }

    public static function isSetInt(term:Term): Bool {
        return switch (term) {
            case Set("[",_): true;
            case _ : false;
        }
    }

    public static function isSameSet(a:Term, b:Term): Bool {
        return switch (a) {
            case Set(aType, _):
            switch (b) {
                case Set(bType,_): aType == bType;
                case _: false;
            }
            case _ : false;
        }
    }

    
    // merge set
    public static function setMerge(a:Array<Term>, b:Array<Term>): Array<Term> {
        var merged = a;

        for(iB in b) {
            var hasB = merged.filter(iMerged -> TermUtils.equal(iMerged, iB)).length > 0;
            if (!hasB) {
                merged.push(iB);
            }
        }

        return merged;
    }

    public static function setMerge2(a:Term, b:Term): Term {
        switch (a) {
            case Set("[", sa):
            switch (b) {
                case Set("[", sb):
                return Set("[", setMerge(sa, sb));
                case _:
                throw "Invalid set merge!";
            }
            case Set("{", sa):
            switch (b) {
                case Set("{", sb):
                return Set("{", setMerge(sa, sb));
                case _:
                throw "Invalid set merge!";
            }
            case _:
            throw "Invalid set merge!";
        }
    }

    // reduces/foldes term
    // ex: ( a & b & (a & c) )  ====>  ( a & b & c )
    public static function fold(foldedType:String, extInt:Term):Term {
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

    // checks if the term encodes a op
    public static function isOp(term:Term):Bool {
        return switch (term) {
            case Name(n): n.charAt(0) == '^';
            default: false;
        }
    }

    // computes structural complexity
    // I define structural complexity as a complexity where compositions  & , &&, |, - etc get extra complexity to bias system
    public static function calcStructComplexity(term:Term): Float {
        // helper to compute complexity of content of compound, etc
        function calcComplexityOfArr(arr:Array<Term>):Float {
            var c = 0.0;
            for(iContent in arr) {
                c += calcStructComplexity(iContent);
            }
            return c;
        }
        
        return switch term {
            case Name(n): 1;
            case ImgWild: 0;
            case Compound(type,content):
            var c = calcComplexityOfArr(content);
            switch type {
                case x if (x == "&" || x == "&&" || x == "-" || x == "|"):
                c+=3.0;
                case _:
                c+=1.0;
            }
            c;
            case Cop(_, subj, pred): calcStructComplexity(subj)+calcStructComplexity(pred)+1.0;
            case Img(base, content):
            calcComplexityOfArr(content)+1.0;
            case Prod(content):
            calcComplexityOfArr(content)+1.0;
            case Var(type,name): 0;
            case Str(content): 1;
            case Set(type, content):
            calcComplexityOfArr(content)+1.0;
        }
    }
}
