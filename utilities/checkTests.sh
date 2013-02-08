export D=`grep "rror\|ssert\|bgebr\|ehler" $1 | wc -l`
export S=`pcregrep -M "sat\n" $1 | wc -l`
export U=`pcregrep -M "unsat\n" $1 | wc -l`
export N=`grep "Testing" $1 | wc -l`
echo "Tested/ing: $N"
echo "Solved: $S"
echo "Sat: $(($S-$U))"
echo "Usat: $U"
echo "Timeout: $(($N-$S-$D))"
echo "Wrong Results: `grep "err" $1 |wc -l`"
echo "Errors: `grep "ssert\|bgebr\|ehler" $1 |wc -l `"
