// interactive shell, is used like gdb
class Interactive {
    public static function main() {
        var reasoner = new Sq2();
        reasoner.conclusionStrArr = []; // enable output logging

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
