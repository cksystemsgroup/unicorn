for NAME in 1 p1 p25 p50 p75 p100
do
    echo $NAME
    ./target/debug/unicorn qubot btor2_files/sat_ratio_experiments/$NAME.btor2 --from-btor2 --out btor2_files/sat_ratio_experiments/qubos/$NAME.unicorn
    ./target/debug/unicorn beator btor2_files/sat_ratio_experiments/$NAME.btor2 --from-btor2 --dimacs --bitblast --out btor2_files/sat_ratio_experiments/cnfs/$NAME.cnf
    echo
done
