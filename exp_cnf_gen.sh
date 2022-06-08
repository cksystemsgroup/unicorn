for WORDSIZE in 8 16 24 32 40 48 56 64
do
    for OPERATOR in add and div eq ite mul not rem sub ult
    do
        echo $OPERATOR $WORDSIZE
        ./target/debug/unicorn beator btor2_files/${WORDSIZE}bit/$OPERATOR.btor2 --from-btor2 --dimacs --bitblast --out btor2_files/cnfs/$WORDSIZE\_$OPERATOR.cnf

        echo
    done
done