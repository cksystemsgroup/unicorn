use super::symbolic_state::QueryResult;
use crate::util::{mean, mean_with_floating_point, median_of_sorted, mode};
use bytesize::ByteSize;
use itertools::Itertools;
use std::convert::TryFrom;
use std::{collections::LinkedList, fmt::Display, time::Duration};

#[derive(Debug, Clone, Copy)]
struct Path {
    pub executed_instructions: u64,
    pub symbolic_beqs: u64,
    pub aborted: bool,
}

#[derive(Debug, Clone)]
pub struct Profiler {
    executed_instructions: u64,
    execution_time: Option<Duration>,
    allocated_memory: Option<ByteSize>,
    true_beq_branches: u64,
    false_beq_branches: u64,
    branch_queries: u64,
    total_queries: u64,
    sat_query_results: u64,
    unsat_query_results: u64,
    unknown_query_results: u64,
    paths_discovered: u64,
    symbolic_beqs: u64,
    solver_times: LinkedList<Duration>,
    path_depths: LinkedList<Path>,
}

impl Default for Profiler {
    fn default() -> Self {
        Self::new()
    }
}

impl Profiler {
    pub fn new() -> Self {
        Self {
            executed_instructions: 0,
            execution_time: None,
            allocated_memory: None,
            true_beq_branches: 0,
            false_beq_branches: 0,
            branch_queries: 0,
            total_queries: 0,
            sat_query_results: 0,
            unsat_query_results: 0,
            unknown_query_results: 0,
            paths_discovered: 1, // one concrete execution path is always discovered per default
            symbolic_beqs: 0,
            solver_times: LinkedList::new(),
            path_depths: LinkedList::new(),
        }
    }

    pub fn merge_with(&mut self, rhs: &mut Self) {
        self.executed_instructions += rhs.executed_instructions;
        assert!(
            self.execution_time.is_none() && rhs.execution_time.is_none(),
            "can not merge execution times in profile"
        );
        assert!(
            self.allocated_memory.is_none() && rhs.allocated_memory.is_none(),
            "can not merge allocated memory sizes in profile",
        );
        self.true_beq_branches += rhs.true_beq_branches;
        self.false_beq_branches += rhs.false_beq_branches;
        self.branch_queries += rhs.branch_queries;
        self.total_queries += rhs.total_queries;
        self.sat_query_results += rhs.sat_query_results;
        self.unsat_query_results += rhs.unsat_query_results;
        self.unknown_query_results += rhs.unknown_query_results;
        self.paths_discovered += rhs.paths_discovered - 1;
        self.symbolic_beqs += rhs.symbolic_beqs;
        self.solver_times.append(&mut rhs.solver_times);
        self.path_depths.append(&mut rhs.path_depths);
    }

    pub fn instruction_executed(&mut self) {
        self.executed_instructions += 1;
    }

    pub fn took_beq_branch(&mut self, truth: bool) {
        if truth {
            self.true_beq_branches += 1;
        } else {
            self.false_beq_branches += 1;
        }
    }

    pub fn symbolic_path_explosion(&mut self) {
        self.paths_discovered += 1;
    }

    pub fn allocated_memory(&mut self, size: ByteSize) {
        self.allocated_memory = Some(size);
    }

    pub fn symbolic_execution_took(&mut self, time: Duration) {
        self.execution_time = Some(time);
    }

    pub fn solved_query(&mut self, time: Duration, result: &QueryResult) {
        self.solver_times.push_back(time);

        self.total_queries += 1;

        match result {
            &QueryResult::Sat(_) => self.sat_query_results += 1,
            QueryResult::UnSat => self.unsat_query_results += 1,
            QueryResult::Unknown => self.unknown_query_results += 1,
        };
    }

    pub fn solved_branch_decision_query(&mut self) {
        self.branch_queries += 1;
    }

    pub fn beq_with_symbolic_condition(&mut self) {
        self.symbolic_beqs += 1;
    }

    pub fn end_of_path(&mut self, executed_instructions: u64) {
        self.path_depths.push_back(Path {
            executed_instructions,
            symbolic_beqs: self.symbolic_beqs,
            aborted: false,
        });

        self.reset_branch_counters();
    }

    pub fn aborted_path_exploration(&mut self, executed_instructions: u64) {
        self.path_depths.push_back(Path {
            executed_instructions,
            symbolic_beqs: self.symbolic_beqs,
            aborted: true,
        });

        self.reset_branch_counters();
    }

    fn reset_branch_counters(&mut self) {
        self.symbolic_beqs = 0;
    }
}

impl Display for Profiler {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let total_branches = self.true_beq_branches + self.false_beq_branches;
        let total_queries =
            self.sat_query_results + self.unsat_query_results + self.unknown_query_results;

        fn percent(total: u64, part: u64) -> f64 {
            if total == 0 {
                0.0
            } else {
                (part as f64) / (total as f64) * 100.0
            }
        }

        fn to_duration(nanos: u128) -> Duration {
            Duration::from_nanos(u64::try_from(nanos).expect("duration should fit into u64"))
        }

        writeln!(f, "instructions:     {}", self.executed_instructions)
            .and_then(|_| {
                if let Some(execution_time) = self.execution_time {
                    let solver_time: Duration = self.solver_times.iter().sum();

                    let solver_time =
                        u64::try_from(solver_time.as_nanos()).expect("should fit into u64");

                    let path_exploration = u64::try_from(execution_time.as_nanos())
                        .expect("should fit into u64")
                        - solver_time;

                    writeln!(
                        f,
                        "execution time:   path exploration: {:?}({:.2}%)  solver: {:?}({:.2}%)",
                        to_duration(path_exploration.into()),
                        percent(solver_time + path_exploration, path_exploration),
                        to_duration(solver_time.into()),
                        percent(solver_time + path_exploration, solver_time)
                    )
                } else {
                    Ok(())
                }
            })
            .and_then(|_| {
                if let Some(allocated_memory) = self.allocated_memory {
                    writeln!(f, "allocated memory: {}", allocated_memory)
                } else {
                    Ok(())
                }
            })
            .and_then(|_| {
                writeln!(
                    f,
                    "branch decisions: true: {}({:.2}%)  false: {}({:.2}%)",
                    self.true_beq_branches,
                    percent(total_branches, self.true_beq_branches),
                    self.false_beq_branches,
                    percent(total_branches, self.false_beq_branches),
                )
            })
            .and_then(|_| {
                let aborted = self.path_depths.iter().filter(|p| p.aborted).count();
                let explored = self.path_depths.len() - aborted;

                writeln!(
                    f,
                    "paths:            discovered: {}  explored: {}({:.2}%)  aborted: {}({:.2}%)",
                    self.paths_discovered,
                    explored,
                    percent(
                        self.paths_discovered,
                        u64::try_from(explored).expect("should fit into u64")
                    ),
                    aborted,
                    percent(
                        self.paths_discovered,
                        u64::try_from(aborted).expect("should fit into u64")
                    )
                )
            })
            .and_then(|_| {
                if self.path_depths.is_empty() {
                    writeln!(
                        f,
                        "  instructions:       min: 0  max: 0  mean: 0  median: 0  mode: 0"
                    )
                } else {
                    let sorted = self
                        .path_depths
                        .iter()
                        .map(|path| path.executed_instructions)
                        .sorted()
                        .collect_vec();

                    writeln!(
                        f,
                        "  instructions:       min: {}  max: {}  mean: {}  median: {}  mode: {}",
                        sorted[0],
                        sorted[sorted.len() - 1],
                        mean_with_floating_point(&sorted).expect("sorted has at least one element"),
                        median_of_sorted(&sorted).expect("sorted has at least one element"),
                        mode(&sorted).expect("sorted has to have at least one element")
                    )
                }
            })
            .and_then(|_| {
                if self.path_depths.is_empty() {
                    writeln!(
                        f,
                        "  symbolic branches:  min: 0  max: 0  mean: 0  median: 0  mode: 0"
                    )
                } else {
                    let sorted = self
                        .path_depths
                        .iter()
                        .map(|path| path.symbolic_beqs)
                        .sorted()
                        .collect_vec();

                    writeln!(
                        f,
                        "  symbolic branches:  min: {}  max: {}  mean: {}  median: {}  mode: {}",
                        sorted[0],
                        sorted[sorted.len() - 1],
                        mean_with_floating_point(&sorted).expect("sorted has at least one element"),
                        median_of_sorted(&sorted).expect("sorted has at least one element"),
                        mode(&sorted).expect("sorted has to have at least one element")
                    )
                }
            })
            .and_then(|_| writeln!(f, "SMT queries:      {}", self.total_queries))
            .and_then(|_| {
                let bug = self.total_queries - self.branch_queries;

                writeln!(
                    f,
                    "  trigger:        branch: {}({:.2}%)  bug: {}({:.2}%)",
                    self.branch_queries,
                    percent(self.total_queries, self.branch_queries),
                    bug,
                    percent(self.total_queries, bug),
                )
            })
            .and_then(|_| {
                writeln!(
                    f,
                    "  results:        sat: {}({:.2}%)  unsat: {}({:.2}%)  unknown: {}({:.2}%)",
                    self.sat_query_results,
                    percent(total_queries, self.sat_query_results),
                    self.unsat_query_results,
                    percent(total_queries, self.unsat_query_results),
                    self.unknown_query_results,
                    percent(total_queries, self.unknown_query_results),
                )
            })
            .and_then(|_| {
                if self.solver_times.is_empty() {
                    write!(
                        f,
                        "  took:           min: 0s  max: 0s  mean: 0s  median: 0s  mode: 0s"
                    )
                } else {
                    let sorted = self
                        .solver_times
                        .iter()
                        .map(|t| t.as_nanos())
                        .sorted()
                        .collect_vec();

                    write!(
                    f,
                    "  took:           min: {:?}  max: {:?}  mean: {:?}  median: {:?}  mode: {:?}",
                    to_duration(sorted[0]),
                    to_duration(sorted[sorted.len() - 1]),
                    to_duration(mean(&sorted).expect("branches has at least one element")),
                    to_duration(
                        median_of_sorted(&sorted).expect("branches has at least one element")
                    ),
                    to_duration(*mode(&sorted).expect("branches has to have at least one element"))
                )
                }
            })
    }
}
