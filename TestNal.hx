import sys.io.File;
import sys.FileSystem;

// automatic test which iterates and checks all *.nal files
class TestNal {
    public static function main() {
        var nalTestFileNames :Array<String> = FileSystem.readDirectory(".").filter(iname -> iname.substr(0, 4) == "Test" && iname.substr(iname.length-4) == ".nal");
        for (iNalFileName in nalTestFileNames) {
            var expectedWithTvNarsese:Map<String, Bool> = new Map<String, Bool>(); // expected narsese with TV, flag tells if it occurred

            var reasoner = new Sq2();
            reasoner.answerHandler = new TestAnswerHandler(expectedWithTvNarsese); // install Q&A handler

            reasoner.conclusionStrArr = []; // enable output logging

            // loads narsese from file
            {
                var nalFileContent = File.getContent(iNalFileName);

                var nalLines = nalFileContent.split("\r\n");
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
                    }
                    else if(iNalLine.substring(0, 2) == "//") {} // ignore commented lines
                    else {
                        reasoner.input(iNalLine);
                    }
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
                    Sys.println('FAILED: failed because not all expects with TV were fullfilled');
                    return;
                }
            }
        }

        Sys.println("SUCCESS!!!");
    }
}

class TestAnswerHandler implements Sq2.AnswerHandler {
    public var expectedWithTvNarsese:Map<String, Bool>;

    public function new(expectedWithTvNarsese:Map<String, Bool>) {
        this.expectedWithTvNarsese = expectedWithTvNarsese;
    }

    public function report(sentence:Sq2.Sentence) {
        if (expectedWithTvNarsese.exists(sentence.convToStr())) {
            expectedWithTvNarsese.set(sentence.convToStr(), true); // did occur
        }
    }
}
