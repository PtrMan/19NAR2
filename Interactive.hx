/*
Copyright 2019 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

import sys.io.File;

// interactive shell, is used like gdb
class Interactive {
    public static function main() {
        var reasoner = new Sq2();
        reasoner.conclusionStrArr = []; // enable output logging

        if (Sys.args().length > 0) {
            var pathToLoad = Sys.args()[0];
            var nalFileContent = File.getContent(pathToLoad);

            var nalLines = nalFileContent.split("\r\n");
            for (iNalLine in nalLines) {
                trace(iNalLine); // debug read line
                reasoner.input(iNalLine);
            }
        }

        while(true) {
            var inputLine: String = Sys.stdin().readLine();

            if (inputLine.charAt(0) == "!" && inputLine.charAt(1) == "s") { // step
                var steps = Std.parseInt(inputLine.substring(2, inputLine.length));
                reasoner.process(steps);
            }
            else if (inputLine.charAt(0) == "!" && inputLine.charAt(1) == "t") { // show all tasks
                reasoner.workingSet.debug();
            }
            else if (inputLine == "!d 1") { // enable debug conclusions
                Sq2.Config.debug_derivations = true;
            }
            else if (inputLine == "!d 0") { // disable debug conclusions
                Sq2.Config.debug_derivations = false;
            }
            else {
                reasoner.input(inputLine);
            }

        }
    }
}
