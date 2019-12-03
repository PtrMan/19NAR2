class Utils {
    public static function contains(arr:Array<Term>, other:Term):Bool {
        return arr.filter(function(x) {return TermUtils.equal(x, other);}).length > 0;
    }

    public static function min(a:Int, b:Int): Int {
        return a < b ? a : b;
    }
}
