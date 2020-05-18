
// helper to directly output stuff to console
class TerminalOut {
    public static function out(msg:String) {
        // don't do this for javascript target!
        #if (!js_es)
        Sys.println(msg);
        #end
    }
}
