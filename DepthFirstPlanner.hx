import Executive;

// planner which keeps track of a "front" of goals with a table of goals which is ordered by priority
class DepthFirstPlanner {
    public var table:GoalTable = new GoalTable();

    public var exec:Executive; // executive wired to the planner

    public var debugGoalSystem:Bool = true;

    public function new() {}

    public function step() {
        if(table.items.length == 0) {
            return; // nothing to do
        }

        var sampledItem: GoalTableItem = table.items[0];
        var sampledGoal:ActiveGoal2 = sampledItem.goal;
        table.items = table.items.slice(1);

        // derive conclusion goals
        if (sampledGoal.condOps.ops.length == 0) {
            Dbg.dbg(debugGoalSystem, 'goalsystem: GOAL DERIVATION');

            var selGoalEvent:Term = sampledGoal.condOps.cond.events[0]; // select first event of par events
            Dbg.dbg(debugGoalSystem, 'goalsystem: sel goal = '+TermUtils.convToStr(selGoalEvent)+"!");

            var matchingImplSeqs:Array<ImplSeq> = exec.mem.queryByPredicate(selGoalEvent);
            for(iMatchedImplSeq in matchingImplSeqs) {
                Dbg.dbg(debugGoalSystem, 'goalsystem: matching impl seq = '+iMatchedImplSeq.convToStr());
            }

            // we need to derive goals from matching implSeqs by goal deduction
            // a =/> b.
            // b!
            // |- ded
            // a!
            for(iImplSeq in matchingImplSeqs) {
                var tvCompound = new Tv(iImplSeq.calcFreq(), iImplSeq.calcConf());
                var tvComponent = sampledGoal.desire;
                var tvConcl = Tv.deduction(tvCompound, tvComponent);
                
                var stampConcl = Stamp.merge(sampledGoal.stamp, iImplSeq.stamp);
                
                // TODO< we need to deal with multiple condops! >
                var goal:ActiveGoal2 = new ActiveGoal2(iImplSeq.condops[0], tvConcl, stampConcl, sampledGoal.creationTime);
                submitGoal(goal, sampledItem.prio * 0.9);
            }
        }
    }

    public function submitGoal(goal:ActiveGoal2, priority:Float) {
        if (goal.condOps.ops.length == 0) {
            submitGoal3(goal, priority);
        }
        else { // case with ops
            if (goal.condOps.cond.events.length > 0) { // must have cond events!
                // (a &/ ^x)!
                // |- DesireDed (deduction)   (structural deduction)
                // a!
                var condOpsConcl = new CondOps(goal.condOps.cond, []); // split off ops
                var desireConcl = Tv.structDeduction(goal.desire);
                
                var goalConcl:ActiveGoal2 = new ActiveGoal2(condOpsConcl, desireConcl, goal.stamp, goal.creationTime);
                submitGoal3(goalConcl, priority);
            }
        }
    }

    public function submitGoal3(goal:ActiveGoal2, priority:Float) {
        table.items.push(new GoalTableItem(goal, priority));

        table.items.sort((a, b) -> Std.int(a.prio - b.prio)); // force sorted by priority!
        table.items.slice(0, 200); // keep under AIKR
    }

    // main for testing
    public static function main() {
        var reasoner = new Nar(null);

        reasoner.input("<(<a --> A> &/ <({SELF} * a0) --> ^a> ) =/> <b --> B>>.");
        reasoner.input("<(<z --> Z> &/ <({SELF} * a0) --> ^a> ) =/> <a --> A>>.");

        
        var planner:DepthFirstPlanner = new DepthFirstPlanner();
        planner.exec = reasoner.executive; // wire up

        {
            var goalTerm = Term.Cop("-->", Term.Name("b"), Term.Name("B"));
            var tv:Tv = new Tv(1.0, 0.98);
            var stamp = planner.exec.createStamp();
            var currentTime = 0; // TODO< real time >

            var goalCondOp:CondOps = new CondOps(new Par([goalTerm]), []);

            var goal:ActiveGoal2 = new ActiveGoal2(goalCondOp, tv, stamp, currentTime);

            planner.submitGoal3(goal, 1.0);
        }


        planner.step();
        planner.step();
        planner.step();
    }
}


// table with active goals, ordered by priority
class GoalTable {
    public var items:Array<GoalTableItem> = [];

    public function new() {}
}

class GoalTableItem {
    
    public var prio:Float; // priority
    public var goal:ActiveGoal2; // actual goal

    public function new(goal, prio) {
        this.goal = goal;
        this.prio = prio;
    }
}
