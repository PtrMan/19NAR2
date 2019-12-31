/*
Copyright 2019 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

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

    public static function revision(a: Tv, b: Tv): Tv {
        var w1 = c2w(a.conf);
        var w2 = c2w(b.conf);
        var w = w1 + w2;
        return new Tv((w1 * a.freq + w2 * b.freq) / w, w2c(w));
    }

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

    
    public static function calcExp(freq:Float, conf:Float) {
        return (freq - 0.5) * conf + 0.5;
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

    static function c2w(c: Float): Float {
        var horizon = 1.0;
        return horizon * c / (1.0 - c);
    }
}