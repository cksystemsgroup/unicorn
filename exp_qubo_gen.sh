
for WORDSIZE in 8 16 24 32 40 48 56 64
do
    for OPERATOR in add and div eq ite mul not rem sub ult
    do
        echo $OPERATOR $WORDSIZE
        ./target/debug/unicorn qubot btor2_files/${WORDSIZE}bit/$OPERATOR.btor2 --from-btor2 --out btor2_files/qubos/$WORDSIZE\_$OPERATOR.unicorn
        echo
    done
done