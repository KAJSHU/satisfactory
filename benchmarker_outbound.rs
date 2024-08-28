/*!
Copyright 2024 KAJSHU

Licensed under the TIG Benchmarker Outbound Game License v1.0 (the "License"); you 
may not use this file except in compliance with the License. You may obtain a copy 
of the License at

https://github.com/tig-foundation/tig-monorepo/tree/main/docs/licenses

Unless required by applicable law or agreed to in writing, software distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied. See the License for the specific
language governing permissions and limitations under the License.
*/

use rand::{rngs::StdRng, Rng, SeedableRng};
use std::collections::HashMap;
use tig_challenges::satisfiability::*;

pub fn solve_challenge(challenge: &Challenge) -> anyhow::Result<Option<Solution>> {
    let mut rng = StdRng::seed_from_u64(challenge.seeds[0] as u64);

    let num_vars = challenge.difficulty.num_variables;
    let mut p_single = vec![false; num_vars];
    let mut n_single = vec![false; num_vars];

    let mut clauses = Vec::with_capacity(challenge.clauses.len());
    let mut dead = false;

    loop {
        let mut done = true;
        clauses.clear();

        for clause in &challenge.clauses {
            let mut temp_clause = Vec::with_capacity(clause.len());
            let mut skip = false;

            for (i, &literal) in clause.iter().enumerate() {
                let var_index = (literal.abs() - 1) as usize;

                if (p_single[var_index] && literal > 0)
                    || (n_single[var_index] && literal < 0)
                    || clause[(i + 1)..].contains(&-literal)
                {
                    skip = true;
                    break;
                } else if p_single[var_index] || n_single[var_index] || clause[(i + 1)..].contains(&literal) {
                    done = false;
                    continue;
                } else {
                    temp_clause.push(literal);
                }
            }

            if skip {
                done = false;
                continue;
            }

            match &temp_clause[..] {
                [literal] => {
                    let var_index = (literal.abs() - 1) as usize;
                    if literal > 0 {
                        if n_single[var_index] {
                            dead = true;
                            break;
                        } else {
                            p_single[var_index] = true;
                        }
                    } else {
                        if p_single[var_index] {
                            dead = true;
                            break;
                        } else {
                            n_single[var_index] = true;
                        }
                    }
                }
                [] => {
                    dead = true;
                    break;
                }
                _ => clauses.push(temp_clause),
            }
        }

        if dead {
            return Ok(None);
        }

        if done {
            break;
        }
    }

    let num_clauses = clauses.len();
    let mut p_clauses = vec![Vec::with_capacity(num_clauses / num_vars + 1); num_vars];
    let mut n_clauses = vec![Vec::with_capacity(num_clauses / num_vars + 1); num_vars];
    let mut variables = vec![false; num_vars];

    for var_index in 0..num_vars {
        variables[var_index] = if p_single[var_index] {
            true
        } else if n_single[var_index] {
            false
        } else {
            rng.gen_bool(0.5)
        };
    }

    let mut num_good_so_far = vec![0; num_clauses];

    for (i, clause) in clauses.iter().enumerate() {
        for &literal in clause {
            let var_index = (literal.abs() - 1) as usize;
            if literal > 0 {
                p_clauses[var_index].push(i);
                if variables[var_index] {
                    num_good_so_far[i] += 1;
                }
            } else {
                n_clauses[var_index].push(i);
                if !variables[var_index] {
                    num_good_so_far[i] += 1;
                }
            }
        }
    }

    let mut residual = Vec::with_capacity(num_clauses);
    let mut residual_indices = HashMap::with_capacity(num_clauses);

    for (i, &num_good) in num_good_so_far.iter().enumerate() {
        if num_good == 0 {
            residual.push(i);
            residual_indices.insert(i, residual.len() - 1);
        }
    }

    let mut attempts = 0;

    while attempts < num_vars * 25 {
        if residual.is_empty() {
            break;
        }

        let i = residual[0];
        let mut min_sad = num_clauses;
        let mut v_min_sad = Vec::new();

        for &literal in &clauses[i] {
            let var_index = (literal.abs() - 1) as usize;
            let mut sad = 0;

            let clause_indices = if variables[var_index] {
                &p_clauses[var_index]
            } else {
                &n_clauses[var_index]
            };

            for &clause_index in clause_indices {
                if num_good_so_far[clause_index] == 1 {
                    sad += 1;
                    if sad > min_sad {
                        break;
                    }
                }
            }

            if sad < min_sad {
                min_sad = sad;
                v_min_sad.clear();
                v_min_sad.push(var_index);
            } else if sad == min_sad {
                v_min_sad.push(var_index);
            }
        }

        let v = if min_sad == 0 {
            *v_min_sad.choose(&mut rng).unwrap()
        } else if rng.gen_bool(0.5) {
            let literal = clauses[i][rng.gen_range(0..clauses[i].len())];
            (literal.abs() - 1) as usize
        } else {
            *v_min_sad.choose(&mut rng).unwrap()
        };

        if variables[v] {
            for &clause_index in &n_clauses[v] {
                num_good_so_far[clause_index] += 1;
                if num_good_so_far[clause_index] == 1 {
                    let last = residual.pop().unwrap();
                    let i = residual_indices.remove(&clause_index).unwrap();
                    if i < residual.len() {
                        residual[i] = last;
                        residual_indices.insert(last, i);
                    }
                }
            }

            for &clause_index in &p_clauses[v] {
                if num_good_so_far[clause_index] == 1 {
                    residual.push(clause_index);
                    residual_indices.insert(clause_index, residual.len() - 1);
                }
                num_good_so_far[clause_index] -= 1;
            }
        } else {
            for &clause_index in &n_clauses[v] {
                if num_good_so_far[clause_index] == 1 {
                    residual.push(clause_index);
                    residual_indices.insert(clause_index, residual.len() - 1);
                }
                num_good_so_far[clause_index] -= 1;
            }

            for &clause_index in &p_clauses[v] {
                num_good_so_far[clause_index] += 1;
                if num_good_so_far[clause_index] == 1 {
                    let last = residual.pop().unwrap();
                    let i = residual_indices.remove(&clause_index).unwrap();
                    if i < residual.len() {
                        residual[i] = last;
                        residual_indices.insert(last, i);
                    }
                }
            }
        }

        variables[v] = !variables[v];
        attempts += 1;
    }

    Ok(Some(Solution { variables }))
}

#[cfg(feature = "cuda")]
mod gpu_optimisation {
    use super::*;
    use cudarc::driver::*;
    use std::{collections::HashMap, sync::Arc};
    use tig_challenges::CudaKernel;

    // set KERNEL to None if algorithm only has a CPU implementation
    pub const KERNEL: Option<CudaKernel> = None;

    // Important! your GPU and CPU version of the algorithm should return the same result
    pub fn cuda_solve_challenge(
        challenge: &Challenge,
        dev: &Arc<CudaDevice>,
        mut funcs: HashMap<&'static str, CudaFunction>,
    ) -> anyhow::Result<Option<Solution>> {
        solve_challenge(challenge)
    }
}

#[cfg(feature = "cuda")]
pub use gpu_optimisation::{cuda_solve_challenge, KERNEL};