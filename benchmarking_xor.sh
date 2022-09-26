!/bin/sh

current_dir=$(pwd)

> times.txt
for entry in $(pwd)/SMTInterpolTest/test/xor/*
do
  f="$(basename -- $entry)"
  echo "$f"

  start=$(date +%s.%3N)
  /home/lena/eclipse-java-2022-03-R-linux-gtk-x86_64/eclipse/plugins/org.eclipse.justj.openjdk.hotspot.jre.full.linux.x86_64_17.0.2.v20220201-1208/jre/bin/java -Dfile.encoding=UTF-8 -classpath /"${current_dir}"/SMTInterpol/bin:/"${current_dir}"/SMTInterpol/lib/jh-javacup-1.2.jar:/"${current_dir}"/Library-SMTLIB/bin de.uni_freiburg.informatik.ultimate.smtinterpol.Main "${entry}"
  end=$(date +%s.%3N)

  duration=$(echo "scale=3; $end - $start" | bc)
  echo "$f : $duration" >> times.txt
done


