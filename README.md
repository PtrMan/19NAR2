# Requirements

It requires Haxe 4.0.X and was tested with Haxe 4.0.5.

The Procedural Tests need the java support library for the Java backend of the Haxe compiler. Haxe will promt the user if it is not installed.
Install it with

> haxelib install hxjava 4.0.0-alpha 

The procedural test require a JDK to compile the transpiled Java sourcecode.


# Attention

Declarative attention is implemented with an agenda like mechanism based on a "flat" table.  Items in the table are ordered by the result of a score function. The score function currently takes decay and confidence of the sentence of the item into account.
New derived conclusions are added to the table if they aren't already present.
The size of the table is limited to a fixed value (to keep it under AIKR).

The size of procedural items of a node(node as the node in ALANN) is limited, items are ordered by exp().
declarative items in the declarative table are ordered by conf.
Ordering by confidence was chosen instead of exp() because the system should be able to consider "negative" evidence equaly (so the function to order the items can't take frequency into account).

# try procedural

enter
> compileRun.bat

(under windows) to run some procedural tests
(doesn't run everything currently).

# try declarative

run

> haxe --run Interactive ALANN_CatBlueSky.nal

to preload a `.nal` file for interactive Q&A. 
(currently Q&A does work with narsese)

and enter `!s5000` to give it 5000 cycles to work on the question(s).
