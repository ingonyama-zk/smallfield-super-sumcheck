export RUSTFLAGS="-Awarnings"

for n in 16 18 20 22 24 26 28; do
    for algo in a1 a4 a1_eq a4_eq; do
        test_name="tests::btf_sumcheck::fq4_tests::benchmark_prover_n${n}_d3_${algo}"
        echo "\nStarting n=${n} d=3 algo=${algo} at $(date '+%Y-%m-%d %H:%M:%S')\n"
        /usr/bin/time -l cargo test --release --package smallfield_sumcheck --lib -- "${test_name}" --exact --show-output -- --nocapture
    done
done