class Stamp {
    // we store the structural origin to avoid doing the same conversion over and over again
    public var structuralOrigins:StructuralOriginsStamp;

    public var ids:Array<haxe.Int64>;

    public function new(ids, structuralOrigins) {
        this.ids = ids;
        this.structuralOrigins = structuralOrigins;
    }

    public static function merge(a:Stamp, b:Stamp): Stamp {
        var ids:Array<haxe.Int64> = [];

        var commonIdx = Utils.min(a.ids.length, b.ids.length);
        for (idx in 0...commonIdx) {
            ids.push(a.ids[idx]);
            ids.push(b.ids[idx]);
        }

        if (a.ids.length > b.ids.length) {
            ids = ids.concat(a.ids.slice(commonIdx, a.ids.length));
        }
        else if (b.ids.length > a.ids.length) {
            ids = ids.concat(b.ids.slice(commonIdx, b.ids.length));
        }

        // limit size of stamp
        var maxStampLength = 2000;
        ids = ids.slice(0, Utils.min(maxStampLength, ids.length));

        return new Stamp(ids, new StructuralOriginsStamp([])); // throw structural orgin of parameters away because a merge invalidates it anyways
    }

    public static function checkOverlap(a:Stamp, b:Stamp, checkStructural=true):Bool {
        // check normal stamp
        for (iA in a.ids) {

            // TODO< speedup with hashmap >
            for (iB in b.ids) {
                if (haxe.Int64.compare(iA, iB) == 0) {
                    return true;
                }
            }
        }

        if (!checkStructural) {
            return false;
        }

        if (checkStructural && !StructuralOriginsStamp.checkOverlap(a.structuralOrigins, b.structuralOrigins)) {
            return false;
        }
        return true;
    }
}
