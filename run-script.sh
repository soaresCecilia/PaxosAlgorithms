#!/bin/bash

scopes="ScopePaxos ScopeVP"
basepath=`pwd`
if [[ ! -z "$1" ]]; then
    basepath=$1
fi

for key in $scopes; do

  outinfo="Scripts/${key}/out/production"
  ininfo="Scripts/${key}/src/com/company/Main.java"
  fullpath="${basepath}/${outinfo}"

  echo "Compiling scope $key"
  javac -d $outinfo $ininfo
  echo "Running scope $key"
  java -Dfile.encoding=UTF-8 -classpath $fullpath com.company.Main ${basepath}/
  echo
  echo
done

outinfo="Scripts/Time/out/production"
ininfo="Scripts/Time/src/com/company/Main.java"
fullpath="${basepath}/${outinfo}"

baseclasspath="${basepath}/"
alloyjars="jars/org.alloytools.alloy.dist.jar"
logapijars="jars/log4j-api-2.3.jar"
logcorejars="jars/log4j-core-2.2.jar"
logimpjars="jars/log4j-slf4j-impl-2.3.jar"
classpath="${baseclasspath}${alloyjars}:${baseclasspath}${logapijars}:${baseclasspath}${logimpjars}:${baseclasspath}${logcorejars}"

echo "Compiling Time"
javac -cp $classpath -d $outinfo $ininfo
echo "Running Time"
java -Dfile.encoding=UTF-8 -cp .:$classpath:$fullpath com.company.Main ${basepath}/
