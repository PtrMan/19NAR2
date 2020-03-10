IF %1.==. GOTO No1
IF %2.==. GOTO No2
GOTO End1

:No1
haxe --java outJava --main Interactive && java -jar outJava\Interactive.jar
GOTO End1
:No2
haxe --java outJava --main Interactive && java -jar outJava\Interactive.jar %1
GOTO End1

:End1
