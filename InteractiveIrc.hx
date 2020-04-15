/*
Copyright 2020 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

import Nar.AnswerHandler;
import sys.io.File;

// IRC client
class InteractiveIrc {
    public static function main() {
        var reasoner = new Nar();
        reasoner.conclusionStrArr = []; // enable output logging
        
        var handler = new IrcHandler2(reasoner); // send IRC messages from IRC to NAR

        var ircClient = new IrcClient(handler);
        reasoner.answerHandler = new AnswerHandler2(ircClient); // send answers from NAR to IRC

        ircClient.connectIrc();

        if (Sys.args().length > 0) {
            var pathToLoad = Sys.args()[0];
            var nalFileContent = File.getContent(pathToLoad);

            var nalLines = nalFileContent.split("\r\n");
            for (iNalLine in nalLines) {
                trace(iNalLine); // debug read line
                reasoner.input(iNalLine);
            }
        }

        var cycleCounter = 0; // for debugging
        
        // run irc client thread
        #if (target.threaded)
        sys.thread.Thread.create(() -> {
            while(true) {
                trace('cycl $cycleCounter');
                cycleCounter++;
    
                ircClient.cycle();
            }
        });
        #end
        
        // reasoner loop
        while(true) {
            reasoner.process(50);
        }
        
    }
}

// handler from IRC to reasoner
class IrcHandler2 implements IrcClient.IrcHandler {
    public function new(reasoner:Nar) {
        this.reasoner = reasoner;
    }
    
    public function msg(originChannel:String, originNick:String, content:String, client:IrcClient) {
        trace('IrcHandler2 msg:$content');

        if (content.charAt(0) == '>') { // is it narsese?
            var narsese = content.substr(1);
            trace('narsese:$narsese');
            reasoner.input(narsese);
        }
    }
    
    public var reasoner:Nar;
}

class AnswerHandler2 implements AnswerHandler {
    public function new(ircClient:IrcClient) {
        this.ircClient = ircClient;
    }
    
    public function report(sentence:Nar.Sentence) {
        ircClient.sendMsg(ircClient.ircChannel, sentence.convToStr());
    }

    public var ircClient:IrcClient;
}
