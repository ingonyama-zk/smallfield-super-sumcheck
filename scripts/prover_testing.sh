export RUSTFLAGS="-Awarnings"

# Start degree 2 tests
echo "\nStarting n=16 d=2 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n16_d2 --exact --show-output -- --nocapture

echo "\nStarting n=18 d=2 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n18_d2 --exact --show-output -- --nocapture

echo "\nStarting n=20 d=2 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n20_d2 --exact --show-output -- --nocapture

echo "\nStarting n=22 d=2 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n22_d2 --exact --show-output -- --nocapture

echo "\nStarting n=24 d=2 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n24_d2 --exact --show-output -- --nocapture

echo "\nStarting n=26 d=2 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n26_d2 --exact --show-output -- --nocapture


# Start degree 3 tests
echo "\nStarting n=16 d=3 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n16_d3 --exact --show-output -- --nocapture

echo "\nStarting n=18 d=3 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n18_d3 --exact --show-output -- --nocapture

echo "\nStarting n=20 d=3 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n20_d3 --exact --show-output -- --nocapture

echo "\nStarting n=22 d=3 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n22_d3 --exact --show-output -- --nocapture

echo "\nStarting n=24 d=3 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n24_d3 --exact --show-output -- --nocapture

echo "\nStarting n=26 d=3 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n26_d3 --exact --show-output -- --nocapture


# Heavy tests at the end
echo "\nStarting n=28 d=2 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n28_d2 --exact --show-output -- --nocapture

echo "\nStarting n=28 d=3 at $(date '+%Y-%m-%d %H:%M:%S')\n"
cargo test --release --package smallfield_sumcheck --lib -- tests::btf_sumcheck::fq4_tests::benchmark_prover_n28_d3 --exact --show-output -- --nocapture