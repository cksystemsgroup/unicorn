use monster::engine;
use std::path::Path;

mod common;

fn execute_riscu_with_monster_solver_name(name: &str) {
    let result = common::compile(Path::new(name)).unwrap();

    let input = Path::new(&result);

    let result = engine::execute(input, engine::Backend::Monster);

    assert!(
        result.is_ok(),
        format!("can symbolically execute '{}' without error", name)
    );

    assert!(std::fs::remove_file(input).is_ok());
}

#[test]
fn execute_riscu_with_monster_solver() {
    execute_riscu_with_monster_solver_name("symbolic/arithmetic.c");
}
