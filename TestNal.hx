import sys.io.File;
import sys.FileSystem;

// automatic test which iterates and checks all *.nal files
class TestNal {
    // /param path where to search *.nal files
    // /return score
    public static function run(path:String): Float {
        var nalTestFileNames :Array<String>;
        
        if (Sys.args().length != 0) { // were the files given as parameters?
            nalTestFileNames = Sys.args();
        }
        else {
            nalTestFileNames = FileSystem.readDirectory(path).filter(iname -> iname.substr(0, 4) == "Test" && iname.substr(iname.length-4) == ".nal");
        }

        var score:Float = 0.0; // sum of score over all NAL test files

        for (iNalFileName in nalTestFileNames) {
            // loads narsese from file
            var nalFileContent = File.getContent(path+"\\"+iNalFileName);
            var nalLines = nalFileContent.split("\r\n");

            var res = runNarAndEvalutate(nalLines, path);
            if (!res.success) {
                Sys.println('FAILED: failed because not all expects with TV were fullfilled');
                return -1.0; // negative because failed
            }
            Sys.println('SCORE=${res.score}'); // print score of this test
            score += res.score; // add up all scores
        }

        return score;
    }

    public static function main() {
        // compute path of program, this is where the test files reside
        var path:String = Sys.programPath();
        // eat away till we hit "\", remove it too
        while(path.length > 0) {
            if(path.charAt(path.length-1) == "\\") {
                break;
            }
            path = path.substr(0, path.length-1); // eat away
        }
        path = path.substr(0, path.length-1); // eat away


        var score:Float = run(path);
        Sys.println('SCORESUM=${score}'); // print score of all tests

        Sys.println("SUCCESS!!!");
    }

    // run nar with the *.nal file and evaluate if it did pass and which score was archived
    public static function runNarAndEvalutate(nalLines:Array<String>, pathToNar:String):{success:Bool,score:Float} {

        var expectedWithTvNarsese:Map<String, Bool> = new Map<String, Bool>(); // expected narsese with TV, flag tells if it occurred
        var expectedWithLowestCyclesNarsese:Map<String, Int> = new Map<String, Int>();

        var reasoner = new Nar(pathToNar);
        reasoner.declarative.answerListener = new TestAnswerListener(expectedWithTvNarsese, expectedWithLowestCyclesNarsese); // install Q&A listener

        reasoner.declarative.conclusionStrArr = []; // enable output logging

        for (iNalLine in nalLines) {
            Sys.println('//input: $iNalLine'); // debug read line

            if (iNalLine.length == 0) {} // ignore empty lines
            else if (iNalLine.charAt(0) == "!" && iNalLine.charAt(1) == "s") { // step
                var steps = Std.parseInt(iNalLine.substring(2, iNalLine.length));
                reasoner.process(steps);
            }
            else if(iNalLine.substring(0, 9)  == "//EXPECT ") {
                var expected:String = iNalLine.substring(9);
                expectedWithTvNarsese.set(expected, false); // false because it didn't occur yet
                expectedWithLowestCyclesNarsese.set(expected, 100000000); // high time because it didn't occur yet
            }
            else if(iNalLine.substring(0, 13)  == "//EXPECTnotv ") {
                var expected:String = iNalLine.substring(13);
                trace('>>$expected<');
                expectedWithLowestCyclesNarsese.set(expected, 100000000); // high time because it didn't occur yet
            }
            else if(iNalLine.substring(0, 2) == "//") {} // ignore commented lines
            else {
                reasoner.input(iNalLine);
            }
        }
        
        { // check if all "expect"-tests were fullfilled
            var allFullfilled = true;
            for(iExpectNarsese in expectedWithTvNarsese.keys()) {
                var wasFullfilled = expectedWithTvNarsese.get(iExpectNarsese);
                allFullfilled = allFullfilled && wasFullfilled;
                if (!wasFullfilled) {
                    Sys.println('$iExpectNarsese was not fullfilled!');
                }
            }

            if (!allFullfilled) {
                return {success:false,score:0.0};
            }
        }


        // compute score by a time-decaying function
        var score:Float = 0.0;
        for(iExpectNarsese in expectedWithLowestCyclesNarsese.keys()) {
            var lowestTime:Int = expectedWithLowestCyclesNarsese.get(iExpectNarsese);
            var decay = 0.01;
            score += Math.exp(-lowestTime*decay); // TODO< incorperate TV conf >
        }

        return {success:true, score:score};
    }
}

class TestAnswerListener implements Nar.AnswerListener {
    public var expectedWithTvNarsese:Map<String, Bool>;
    public var expectedWithLowestCyclesNarsese:Map<String, Int>;

    public function new(expectedWithTvNarsese:Map<String, Bool>, expectedWithLowestCyclesNarsese:Map<String, Int>) {
        this.expectedWithTvNarsese = expectedWithTvNarsese;
        this.expectedWithLowestCyclesNarsese = expectedWithLowestCyclesNarsese;
    }

    public function report(sentence:Nar.Sentence, cycles:Int) {
        if (expectedWithTvNarsese.exists(sentence.convToStr())) {
            expectedWithTvNarsese.set(sentence.convToStr(), true); // did occur
        }

        // (sentences with TV)
        // TODO< set it to the time only if exp is higher! >
        if (expectedWithLowestCyclesNarsese.exists(sentence.convToStr())) {
            expectedWithLowestCyclesNarsese.set(sentence.convToStr(), cycles); // set time
        }

        // (sentences without TV)
        // TODO< set it to the time only if exp is higher! >
        if (expectedWithLowestCyclesNarsese.exists(TermUtils.convToStr(sentence.term)+".")) {
            expectedWithLowestCyclesNarsese.set(TermUtils.convToStr(sentence.term)+".", cycles); // set time
        }
    }
}
