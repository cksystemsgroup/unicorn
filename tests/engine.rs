use monster::engine;
use std::path::Path;

mod common;

fn execute_riscu_with_monster(name: &str, solver: engine::Backend) {
    let result = common::compile(Path::new(name)).unwrap();

    let input = Path::new(&result);

    let result = engine::execute(input, solver);

    assert!(
        result.is_ok(),
        format!("can symbolically execute '{}' without error", name)
    );

    assert!(std::fs::remove_file(input).is_ok());
}

#[test]
fn execute_riscu_with_monster_solver() {
    execute_riscu_with_monster("symbolic/arithmetic.c", engine::Backend::Monster);
    execute_riscu_with_monster("symbolic/if-else.c", engine::Backend::Monster);
}

#[test]
fn execute_riscu_with_boolector_solver() {
    execute_riscu_with_monster("symbolic/arithmetic.c", engine::Backend::Boolector);
    execute_riscu_with_monster("symbolic/if-else.c", engine::Backend::Boolector);
}

#[test]
fn execute_riscu_with_z3_solver() {
    execute_riscu_with_monster("symbolic/arithmetic.c", engine::Backend::Z3);
    execute_riscu_with_monster("symbolic/if-else.c", engine::Backend::Z3);
}
