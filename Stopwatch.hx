/*
Copyright 2020 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

// used to stop the time for instrumentation
class Stopwatch {
    public var startTime:Float=0.0;
    public function new() {}
    public function start() {
        // don't do this for javascript target!
        #if (!js_es)
        startTime = Sys.time();
        #end
    }
    public function retCurrentTimeDiff() {
        // don't do this for javascript target!
        #if (!js_es)
        return Sys.time()-startTime;
        #end
        return 0.0; // return 0 by default on targets where it is not supported!
    }
    public static function createAndStart() {
        var sw = new Stopwatch();
        sw.start();
        return sw;
    }
}