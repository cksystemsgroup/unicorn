use monster::engine;
use std::path::Path;

mod common;

#[test]
fn execute_riscu_with_monster_solver() {
    let result = common::compile(Path::new("symbolic/arithmetic.c")).unwrap();

    let input = Path::new(&result);

    let result = engine::execute(input, engine::Backend::Monster);

    assert!(
        result.is_ok(),
        "can symbolically execute arithmetic.c without error"
    );

    assert!(std::fs::remove_file(input).is_ok());
}
