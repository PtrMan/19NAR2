/*
Copyright 2020 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

import sys.net.Socket;
import sys.net.Host;

class IrcClient {
    public var socket:Socket;

    public var hostname = "chat.freenode.net";
    public var port = 6667;
    public var ircChannel = "#test0004";
    public var ircNicks = ["bot_N00B0R"];

    // initialize IRC, has to get called before anything else is called from the class
    public function connectIrc() {
        var ircNick = ircNicks[0]; // pick first nick for the first try

        trace("connecting to irc...");

        socket = new Socket();
        socket.setTimeout(160.0);
        socket.connect(new Host(hostname), port);
        socket.setFastSend(true);

        trace("connected");

        
        socket.output.writeString('NICK $ircNick\r\n');
        socket.output.writeString('USER $ircNick 0 * :NLU bot\r\n');
        socket.output.writeString('JOIN $ircChannel\r\n');
        socket.output.flush();

        trace("sent request...");

        socket.setBlocking(false);
    }

    public function cycle() {
        trace('enter irc cycle');

        var readBuffer = "";
        while(true) { // loop for reading from socket
            var hasReadAny = false; // was any information read from socket?
            try {

                var read = socket.input.read(1);
                readBuffer += read;
                hasReadAny = true;
                if (readBuffer.charAt(readBuffer.length-1) == "\n") {
                    var line = readBuffer.substring(0, readBuffer.length-1-1); // remove "\r\n"

                    trace(line);

                    {
                        var tokens = line.split(" ");
                        if (tokens[0] == "PING") {
                            socket.output.writeString('PONG ${tokens[1]}\r\n');
                        }
                        else if (tokens[1] == "PRIVMSG") {
                            var channelname = tokens[2]; // name of the channel where the message was sent

                            // search for ":" which is the seperator of the message
                            var msgSepIdx = 0;
                            for(idx in 1...line.length) {
                                if (line.charAt(idx) == ":") {
                                    msgSepIdx = idx;
                                    break;
                                }
                            }

                            var content:String = line.substring(msgSepIdx+1, line.length); // is the message
                            
                            // TODO< parse nick >
                            handler.msg(channelname, "?", content, this);
                        }
                    }
                    
                    readBuffer = "";
                }
                //else {
                    // TODO< sleep >
                //}
            }
            catch (e: Dynamic) {
                // code is from https://stackoverflow.com/a/39293383/388614
                if (Std.is(e, haxe.io.Eof) || e == haxe.io.Eof) { // end of stream
                    // close the socket, etc.
                }
                else if (e == haxe.io.Error.Blocked) {
                    // not an error - this is still a connected socket
                    break;
                }
                else {
                    //trace(e);
                }
            }

            if(!hasReadAny) {
                break;
            }
        }
        
        trace('exit irc cycle');
    }

    public function new(handler:IrcHandler) {
        this.handler = handler;
    }

    public function sendMsg(channelname:String, content:String) {
        socket.output.writeString('PRIVMSG $channelname :$content\r\n');
        socket.output.flush();
    }
    
    /* commented because it just has to show how to use this
    public static function main() {
        var ircClient = new IrcClient();
        ircClient.connectIrc();
        
        while(true) {
            ircClient.cycle();
        }
    }
    */

    public var handler:IrcHandler;
}

// binding for the IRC, connects IRC to the actual functionality
interface IrcHandler {
    // is called when ever a new message is received from IRC
    function msg(originChannel:String, originNick:String, content:String, client:IrcClient):Void;
}
