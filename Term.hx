/*
Copyright 2019 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

// TODO< rename to NarTerm >
enum Term {
    Name(name:String, label0:Bool); // label0 is used to label a name as "psuedo-axiomatic", which can be used to differentiate between "pure" axiomatic-ish terms and NAL terms
    Compound(type:String, content:Array<Term>); // intersection, difference, etc.
    
    // TODO< rename to statement >
    Cop(copula:String, subj:Term, pred:Term); // generalization of anything connected with a copula, for example "-->" "<->" etc.
    Prod(terms:Array<Term>); // product
    Img(base:Term, content:Array<Term>); // image
    ImgWild; // wildcard for image NAL:"_"

    Var(type:String,name:String); // variable, type can be "?","#","$"

    Str(content:String); // "content" , " and \ are escaped
    Set(type:String, content:Array<Term>); // "[" or "{" set
}
