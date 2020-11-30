use std::process::{Command, Stdio};

#[test]
fn test_if_docker_daemon_is_running() {
    let docker_daemon_is_running = Command::new("docker")
        .arg("ps")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false);

    assert!(
        docker_daemon_is_running,
        "check if Docker daemon is running"
    );
}
