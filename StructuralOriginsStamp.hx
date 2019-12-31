/*
Copyright 2019 Robert Wünsche

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

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
