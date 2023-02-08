use anyhow::Result;
use pyo3::prelude::*;
use pyo3::types::IntoPyDict;
use std::collections::HashMap;

pub fn sample_quantum_annealer(path: &str, num_reads: u32, chain_strength: f32) -> Result<()> {
    let py_dwave = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/quantum_annealing/dwave_api.py"
    ));
    let from_python = Python::with_gil(|py| -> PyResult<Py<PyAny>> {
        let app: Py<PyAny> = PyModule::from_code(py, py_dwave, "sample_qubo", "")?
            .getattr("sample_qubo")?
            .into();
        println!("{:?}", app);
        let mut kwargs = HashMap::<&str, String>::new();
        kwargs.insert("path", path.to_string());
        kwargs.insert("num_reads", num_reads.to_string());
        kwargs.insert("chain_strength", chain_strength.to_string());
        app.call(py, (), Some(kwargs.into_py_dict(py)))
    });
    from_python?;

    Ok(())
}
