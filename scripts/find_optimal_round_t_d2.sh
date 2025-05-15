export RUSTFLAGS="-Awarnings"

echo "\nStarting n=16 d=2 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_optimal_round_t_n16_d2 --exact --show-output -- --nocapture

echo "\nStarting n=18 d=2 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_optimal_round_t_n18_d2 --exact --show-output -- --nocapture

echo "\nStarting n=20 d=2 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_optimal_round_t_n20_d2 --exact --show-output -- --nocapture

echo "\nStarting n=22 d=2 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_optimal_round_t_n22_d2 --exact --show-output -- --nocapture