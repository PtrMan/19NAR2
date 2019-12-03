enum Term {
    Name(name:String);
    Compound(type:String, content:Array<Term>); // intersection, difference, etc.
    
    // TODO< rename to statement >
    Cop(copula:String, subj:Term, pred:Term); // generalization of anything connected with a copula, for example "-->" "<->" etc.
    Prod(terms:Array<Term>); // product
    Img(base:Term, content:Array<Term>); // image
    ImgWild; // wildcard for image NAL:"_"

    Var(type:String,name:String); // variable, type can be "?","#","$"

    Str(content:String); // "content" , " and \ are escaped
}
