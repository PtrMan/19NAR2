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

            if (inputLine.charAt(0) == "s") { // step
                var steps = Std.parseInt(inputLine.substring(1, inputLine.length));
                reasoner.process(steps);
            }
            else if (inputLine.charAt(0) == "t") { // show all tasks
                reasoner.workingSet.debug();
            }
            else {
                reasoner.input(inputLine);
            }

        }
    }
}
