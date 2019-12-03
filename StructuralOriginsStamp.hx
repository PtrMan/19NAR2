class StructuralOriginsStamp {
    public var arr:Array<Term> = [];

    public function new(arr) {
        this.arr = arr;
    }

    public static function equal(a:StructuralOriginsStamp, b:StructuralOriginsStamp):Bool {
        if (a.arr.length != b.arr.length) {
            return false;
        }

        for (idx in 0...a.arr.length) {
            if (!TermUtils.equal(a.arr[idx], b.arr[idx])) {
                return false;
            }
        }

        return true;
    }

    public static function checkOverlap(a:StructuralOriginsStamp, b:StructuralOriginsStamp):Bool {
        if (a.arr.length == 0 && b.arr.length == 0) {
            return false; // false because it is a special case because both structural stamps are empty
        }
        return StructuralOriginsStamp.equal(a, b);
    }
}
