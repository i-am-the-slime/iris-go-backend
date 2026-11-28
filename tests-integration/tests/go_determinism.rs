use std::path::Path;

const PROGRAMS: [&str; 6] = [
    "1794568810_traverse_general_applicative",
    "1800300004_record_seen_as_an_object_until_it_must_be_one",
    "1800500004_sorts_by_an_int_key_merge_sort_keys_and_positions",
    "1801100003_tallies_in_an_object_hash_each_key_once",
    "1801300004_callers_that_hand_go_maps_call_variants_of_functions",
    "1801400003_go_maps_keyed_by_tuples_sort_by_a_comparison_of_their_fields",
];

const THREADS: [usize; 3] = [1, 8, 4];

#[test]
fn compiling_a_program_again_writes_the_same_go() {
    for program in PROGRAMS {
        let main = Path::new("fixtures/go").join(program).join("Main.purs");
        let outputs: Vec<String> =
            THREADS.iter().map(|&threads| go_with_threads(&main, threads)).collect();
        for (threads, output) in THREADS.iter().zip(&outputs).skip(1) {
            assert!(
                output == &outputs[0],
                "{program} compiled on {threads} threads differs from its first compilation"
            );
        }
    }
}

fn go_with_threads(main: &Path, threads: usize) -> String {
    let pool = rayon::ThreadPoolBuilder::new().num_threads(threads).build().unwrap();
    let output = pool.install(|| {
        tests_integration::fixtures::go_output(main).map_err(|error| error.to_string())
    });
    output.unwrap_or_else(|error| panic!("{} does not compile: {error}", main.display()))
}
