/*
Copyright 2020 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

import Executive;

// pong2 and pong1 ONA conform implementation as implemented in ONA
class EnvPong1And2 {
    public static function main() {
        runPong1(15000);
    }

    public var szX:Int = 50;
    public var szY:Int = 20;
    public var ballX:Int;
    public var ballY:Int;
    public var batX:Int = 20;
    public var batVX:Int = 0;
    public var batWidth:Int = 6; //"radius", batWidth from middle to the left and right
    public var virtualBatWidth:Int = 6; // bat width used for center computation
    public var vX:Int = 1;
    public var vY:Int = 1;
    public var mulVX:Int = 0; // multiply x velocity by this before moving
    public var hits:Int = 0;
    public var misses:Int = 0;
    public var t:Int=0;

    public var opLeft:SwitchOp;
    public var opRight:SwitchOp;

    public function new() {}


    public function envLoop(reasoner:Nar, iterations:Int) {
        while(true) {
            // DEBUG check for invalid goals
            if(true) {
                for(iStr in GoalSystemDebug.debugAllGoals(reasoner.executive.goalSystem2)) {
                    if (iStr.indexOf("(  )")!=-1) {
                        for(iStr2 in GoalSystemDebug.debugAllGoals(reasoner.executive.goalSystem2)) {
                            TerminalOut.out(iStr2);
                        }

                        throw "goal system contains invalid goal!";
                    }
                }
            }


            if(true) TerminalOut.out('');
            if(true) TerminalOut.out('');
            if(true) TerminalOut.out('');

            t++;
            if(iterations != -1 && t++ > iterations) {
                break;
            }

            /* commented because we don't visualize!
            //fputs("\033[1;1H\033[2J", stdout); //POSIX clear screen
            for(int i=0; i<batX-batWidth+1; i++)
            {
                fputs(" ", stdout);
            }
            for(int i=0; i<batWidth*2-1+MIN(0,batX) ;i++)
            {
                fputs("@", stdout);
            }
            puts("");
            for(int i=0; i<ballY; i++)
            {
                for(int k=0; k<szX; k++)
                {
                    fputs(" ", stdout);
                }
                puts("|");
            }
            for(int i=0; i<ballX; i++)
            {
                fputs(" ", stdout);
            }
            fputs("#", stdout);
            for(int i=ballX+1; i<szX; i++)
            {
                fputs(" ", stdout);
            }
            puts("|");
            for(int i=ballY+1; i<szY; i++)
            {
                for(int k=0; k<szX; k++)
                {
                    fputs(" ", stdout);
                }
                puts("|");
            }
            */

            if(batX <= ballX - virtualBatWidth) {
                if(true) TerminalOut.out('BALL right');
                reasoner.input("<{right}-->ball>. :|:");
            }
            else if(ballX + virtualBatWidth < batX) {
                if(true) TerminalOut.out('BALL right');
                reasoner.input("<{left}-->ball>. :|:");
            }
            else {
                if(true) TerminalOut.out('BALL center');
                reasoner.input("<{center}-->ball>. :|:");
            }
            reasoner.input("<good-->nar>! :|:");

            if(ballX <= 0) {
                vX = 1;
            }
            if(ballX >= szX-1) {
                vX = -1;
            }
            if(ballY <= 0) {
                vY = 1;
            }
            if(ballY >= szY-1) {
                vY = -1;
            }
            if((t%2) == -1) {
                ballX += vX;
            }
            ballX += (vX*mulVX);
            ballY += vY;
            if(ballY == 0) {
                if(Math.abs(ballX-batX) <= batWidth) {
                    reasoner.input("<good-->nar>. :|:");
                    TerminalOut.out("good");
                    hits++;
                }
                else {
                    TerminalOut.out("bad");
                    misses++;
                }
            }
            if(ballY == 0 || ballX == 0 || ballX >= szX-1) {
                ballY = Std.int(szY/2)+Std.random(Std.int(szY/2));
                ballX = Std.random(szX);
                vX = Std.random(2) == 0 ? 1 : -1;
            }
            if(opLeft.triggered) {
                opLeft.triggered = false;
                TerminalOut.out("Exec: op_left");
                batVX = -3;
            }
            if(opRight.triggered) {
                opRight.triggered = false;
                TerminalOut.out("Exec: op_right");
                batVX = 3;
            }
            /*
            if(NAR_Pong_Stop_executed) {
                NAR_Pong_Stop_executed = false;
                TerminalOut.out("Exec: op_stop");
                batVX = 0;
            }*/
            batX=Std.int(Math.max(-batWidth*2,Math.min(szX-1+batWidth,batX+batVX*batWidth/2)));
            var ratio:Float = hits;
            ratio /= (hits + misses);
            TerminalOut.out('PONG  Hits=$hits misses=$misses ratio=$ratio time=$t');

            // debug all goals of goal system
            var debugGoals:Bool = false;
            if(debugGoals) {
                for(iStr in GoalSystemDebug.debugAllGoals(reasoner.executive.goalSystem2)) {
                    TerminalOut.out('  $iStr');
                }
            }
            
            reasoner.executive.step();
        }
    }

    public static function runPong2(iterations:Int) {
        var reasoner = new Nar(null);
        reasoner.executive.randomActProb = 0.05;
        reasoner.executive.deadlineAlgorithm = "dt2plus"; // natural environment

        //var opStop = new SwitchOp("^stop");
        //reasoner.executive.acts.push({mass:1.0, act:opStop});


        reasoner.executive.dbgAnticipationVerbose = true;
        
        var env:EnvPong1And2 = new EnvPong1And2();

        env.opLeft = new SwitchOp("^left");
        reasoner.executive.acts.push({mass:1.0, act:env.opLeft});
        env.opRight = new SwitchOp("^right");
        reasoner.executive.acts.push({mass:1.0, act:env.opRight});

        env.ballX = Std.int(env.szX/2);
        env.ballY = Std.int(env.szY/5);

        env.envLoop(reasoner, iterations);
        

        TerminalOut.out("GoalSystem.goals:");
        // debug all goals of goal system
        if(true) {
            for(iStr in GoalSystemDebug.debugAllGoals(reasoner.executive.goalSystem2)) {
                TerminalOut.out('  $iStr');
            }
        }
    }

    
    public static function runPong1(iterations:Int) {
        var reasoner = new Nar(null);
        reasoner.executive.randomActProb = 0.05;
        reasoner.executive.deadlineAlgorithm = "dt2plus"; // natural environment

        reasoner.executive.dbgAnticipationVerbose = true;
        reasoner.executive.goalSystem2.debugGoalSystem = true;
        
        var env:EnvPong1And2 = new EnvPong1And2();
        env.batWidth = 4;
        env.mulVX = 1; // move ball in x
        env.virtualBatWidth = 0; // has no virtual width

        env.opLeft = new SwitchOp("^left");
        reasoner.executive.acts.push({mass:1.0, act:env.opLeft});
        env.opRight = new SwitchOp("^right");
        reasoner.executive.acts.push({mass:1.0, act:env.opRight});

        env.ballX = Std.int(env.szX/2);
        env.ballY = Std.int(env.szY/5);

        env.envLoop(reasoner, iterations);
        

        TerminalOut.out("GoalSystem.goals:");
        // debug all goals of goal system
        if(true) {
            for(iStr in GoalSystemDebug.debugAllGoals(reasoner.executive.goalSystem2)) {
                TerminalOut.out('  $iStr');
            }
        }
    }
}

// op for switching a boolean on
// used for self-tests, unittests, etc.
class SwitchOp extends Act {
    public var triggered:Bool = false;

    public function new(name:String) {
        super(name);
    }

    public override function exec(args:Array<Term>) {
        triggered = true;
    }
}
