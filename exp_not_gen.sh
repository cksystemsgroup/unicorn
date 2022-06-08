for NAME in p1 p01 p001 p0001 p00001 p000001 p5 p10 p25 p50 p75 p100
do
    echo $NAME
    ./target/debug/unicorn qubot btor2_files/sat_ratio_experiments/not/$NAME.btor2 --from-btor2 --out btor2_files/sat_ratio_experiments/not/qubos/not_$NAME.unicorn
    ./target/debug/unicorn beator btor2_files/sat_ratio_experiments/not/$NAME.btor2 --from-btor2 --dimacs --bitblast --out btor2_files/sat_ratio_experiments/not/cnfs/not_$NAME.cnf
    echo
done
