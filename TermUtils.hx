
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
            case Str(content): Str(content);
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
        }
    }

    public static function isVar(term:Term): Bool {
        return switch (term) {
            case Var(_,_): true;
            case _ : false;
        }
    }

    // checks if the term encodes a op
    public static function isOp(term:Term):Bool {
        return switch (term) {
            case Name(n): n.charAt(0) == '^';
            default: false;
        }
    }
}