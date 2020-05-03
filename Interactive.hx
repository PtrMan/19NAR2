/*
Copyright 2020 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

import sys.io.File;

// interactive shell, is used like gdb
class Interactive {
    public var reasoner:Nar = new Nar(null);

    public function new() {}

    // process a inputLine
    public function processLine(inputLine:String) {
        if (inputLine.length == 0) {} // ignore empty lines
        else if (inputLine.substr(0, 2) == "//") { // ignore comments
        }
        else if (inputLine.charAt(0) == "!" && inputLine.charAt(1) == "s") { // step
            var steps = Std.parseInt(inputLine.substring(2, inputLine.length));
            reasoner.process(steps);
        }
        else if (inputLine == "!d 1") { // enable debug conclusions
            Nar.Config.debug_derivations = true;
        }
        else if (inputLine == "!d 0") { // disable debug conclusions
            Nar.Config.debug_derivations = false;
        }
        else if (inputLine == "!ds 1") { // enable debug stored
            Nar.Config.debug_derived = true;
        }
        else if (inputLine == "!ds 0") { // disable debug stored
            Nar.Config.debug_derived = false;
        }
        else if (inputLine == "!dw") { // debug working set
            // print working set
            Sys.println(reasoner.declarative.workingSet.debug());
        }
        else if (inputLine == "!ds") { // debug summary
            reasoner.declarative.debugSummary();
        }
        else if (inputLine == "!dj") { // debug all judgements
            reasoner.declarative.debugJudgements();
        }
        else if (inputLine == "!pe") { // profiler enable
            Nar.Config.enProfiler = true;
        }
        else if (inputLine == "!r") { // reset
            reasoner.resetMemory();
        }
        else if (inputLine == "!re 0") { // reset default executive
            reasoner.executive = new Executive();
        }
        else if (startsWidth(inputLine, "!edt ")) { // executive decision threshold (set)
            var val:Float = Std.parseFloat(inputLine.substr(5));
            if (Math.isNaN(val)) {
                Sys.println('command error: not a float!');
            }
            else if(val < 0.0 || val > 1.0) {
                Sys.println('command error: decision threshold must be between 0.0 and 1.0!');
            }
            else {
                reasoner.executive.decisionThreshold = val;
            }
        }
        else if (inputLine.substr(0, 3) == "!l ") { // load from file
            var path:String = inputLine.substring(3);
            loadFromFile(path);
        }
        else if (inputLine.length > 0 && inputLine.charAt(0) == "!") {
            Sys.println('unknown command "$inputLine"');
        }
        else {
            reasoner.input(inputLine);
        }
    }

    // loads narsese from file
    public function loadFromFile(pathToLoad:String) {
        var nalFileContent = File.getContent(pathToLoad);

        var nalLines = nalFileContent.split("\r\n");
        for (iNalLine in nalLines) {
            Sys.println('//input: $iNalLine'); // debug read line
            processLine(iNalLine);
        }
    }

    public static function main() {
        var interactive = new Interactive();
        interactive.reasoner.declarative.conclusionStrArr = []; // enable output logging

        // load zero or any number of *.nal files
        for (iArg in Sys.args()) {
            var pathToLoad = iArg;
            interactive.loadFromFile(pathToLoad);
        }

        while(true) {
            var inputLine: String = Sys.stdin().readLine();
            interactive.processLine(inputLine);
        }
    }

    // helper
    private static function startsWidth(str:String, sub:String):Bool {
        return str.substr(0, sub.length) == sub;
    }
}
