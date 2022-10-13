#!/bin/bash

parent=`dirname $PWD`
grandparent=`dirname $parent`

if [[ ! -z "$1" ]]; then
    grandparent=$1
fi

#echo "Running Scope"
#python scope.py

baseclasspath="${grandparent}/"
tlajars="jars/tla2tools.jar"
classpath="${baseclasspath}${tlajars}"

START=$(date +%s)
scopes="scopes/acc3quorum2/ scopes/acc4quorum3/"
for scope in ${scopes}; do
  echo "Running ${scope}"
  for i in `ls ${scope}testing*.tla`; do
    echo "Running Time ${i}"
    java -cp  $classpath -XX:+UseParallelGC -Dtlc2.TLC.ide=vscode tlc2.TLC ${i} -tool -modelcheck -workers 16 -config ${scope}testing.cfg -deadlock
  done
done
END=$(date +%s)
DIFF=$(( $END - $START ))
echo "It took $DIFF seconds"
