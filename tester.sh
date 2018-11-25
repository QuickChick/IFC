for i in `seq $1 $2`; do
  echo "Testing Mutant $i.. with method $3"
  cp Bench.v Tmp.v
  echo "QuickChick (testMutantX_ rSSNI_$3 $i)." >> Tmp.v 
  coqc -R . IFC Tmp.v &> output/output_$3_$i.out
  sleep 2
done

