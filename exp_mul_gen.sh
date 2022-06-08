for i in {0..255}
do 
    touch btor2_files/mul_experiments/$i.btor2
    echo 1 sort bitvec 8 > btor2_files/mul_experiments/$i.btor2
    echo 2 input 1 >> btor2_files/mul_experiments/$i.btor2
    echo 3 input 1 >> btor2_files/mul_experiments/$i.btor2
    echo 4 mul 1 2 3 >> btor2_files/mul_experiments/$i.btor2
    echo 5 constd 1 $i >> btor2_files/mul_experiments/$i.btor2
    echo 6 eq 1 4 5 >> btor2_files/mul_experiments/$i.btor2
    echo 7 bad 6 >> btor2_files/mul_experiments/$i.btor2

    ./target/debug/unicorn beator btor2_files/mul_experiments/$i.btor2 --from-btor2 --dimacs --bitblast --out btor2_files/mul_experiments/cnfs/$i.cnf

    ./target/debug/unicorn qubot btor2_files/mul_experiments/$i.btor2 --from-btor2 --out btor2_files/mul_experiments/qubos/$i.unicorn
done