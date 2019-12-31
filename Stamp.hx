/*
Copyright 2019 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

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

    public function convToStr():String {
        return ""+(ids.map(id -> haxe.Int64.toStr(id)));
    }
}
