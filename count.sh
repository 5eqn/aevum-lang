a=`./build/counter/aevum src/Aevum/Main.idr`
b=`./build/counter/aevum src/Aevum/Path.idr`
c=`./build/counter/aevum src/Aevum/Util.idr`
d=`./build/counter/aevum src/Aevum/Type.idr`
let e=a+b+c+d
echo Total $e lines
echo Main.idr $a lines
echo Path.idr $b lines
echo Util.idr $c lines
echo Type.idr $d lines
