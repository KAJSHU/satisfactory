/*!
Copyright 2024 KAJSHU

Licensed under the TIG Inbound Game License v1.0 or (at your option) any later
version (the "License"); you may not use this file except in compliance with the
License. You may obtain a copy of the License at

https://github.com/tig-foundation/tig-monorepo/tree/main/docs/licenses

Unless required by applicable law or agreed to in writing, software distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied. See the License for the specific
language governing permissions and limitations under the License.
*/

use rand::{rngs::StdRng, Rng, SeedableRng};
use std::collections::{HashMap, HashSet};
use tig_challenges::satisfiability::*;

/// Solve the satisfiability challenge.
pub fn solve_challenge(challenge: &Challenge) -> anyhow::Result<Option<Solution>> {
    let mut rng = StdRng::seed_from_u64(challenge.seeds[0] as u64);
    let num_variables = challenge.difficulty.num_variables;
    let mut p_single = vec![false; num_variables];
    let mut n_single = vec![false; num_variables];

    let mut clauses_ = challenge.clauses.clone();
    let mut clauses: Vec<Vec<i32>> = Vec::with_capacity(clauses_.len());

    let mut dead = false;

    while !dead {
        let mut done = true;
        for c in &clauses_ {
            let mut c_: Vec<i32> = Vec::with_capacity(c.len());
            let mut skip = false;
            for (i, l) in c.iter().enumerate() {
                if (p_single[(l.abs() - 1) as usize] && *l > 0)
                    || (n_single[(l.abs() - 1) as usize] && *l < 0)
                    || c[(i + 1)..].contains(&-l)
                {
                    skip = true;
                    break;
                } else if p_single[(l.abs() - 1) as usize]
                    || n_single[(l.abs() - 1) as usize]
                    || c[(i + 1)..].contains(&l)
                {
                    done = false;
                    continue;
                } else {
                    c_.push(*l);
                }
            }
            if skip {
                done = false;
                continue;
            };
            match c_[..] {
                [l] => {
                    done = false;
                    if l > 0 {
                        if n_single[(l.abs() - 1) as usize] {
                            dead = true;
                            break;
                        } else {
                            p_single[(l.abs() - 1) as usize] = true;
                        }
                    } else {
                        if p_single[(l.abs() - 1) as usize] {
                            dead = true;
                            break;
                        } else {
                            n_single[(l.abs() - 1) as usize] = true;
                        }
                    }
                }
                [] => {
                    dead = true;
                    break;
                }
                _ => {
                    clauses.push(c_);
                }
            }
        }
        if done {
            break;
        } else {
            clauses_ = clauses;
            clauses = Vec::with_capacity(clauses_.len());
        }
    }

    if dead {
        return Ok(None);
    }

    let num_clauses = clauses.len();
    let mut p_clauses: Vec<Vec<usize>> = vec![vec![]; num_variables];
    let mut n_clauses: Vec<Vec<usize>> = vec![vec![]; num_variables];

    let mut variables = vec![false; num_variables];
    for v in 0..num_variables {
        variables[v] = if p_single[v] {
            true
        } else if n_single[v] {
            false
        } else {
            rng.gen_bool(0.5)
        }
    }

    let mut num_good_so_far: Vec<usize> = vec![0; num_clauses];
    for (i, ref c) in clauses.iter().enumerate() {
        for &l in c {
            let var = (l.abs() - 1) as usize;
            if l > 0 {
                p_clauses[var].push(i);
                if variables[var] {
                    num_good_so_far[i] += 1;
                }
            } else {
                n_clauses[var].push(i);
                if !variables[var] {
                    num_good_so_far[i] += 1;
                }
            }
        }
    }

    let mut residual = HashSet::with_capacity(num_clauses);
    for (i, &num_good) in num_good_so_far.iter().enumerate() {
        if num_good == 0 {
            residual.insert(i);
        }
    }

    let mut attempts = 0;
    while attempts < num_variables * 35 {
        if let Some(&i) = residual.iter().next() {
            let mut min_sad = clauses.len();
            let mut v_min_sad = Vec::with_capacity(clauses[i].len());
            let c = &clauses[i];
            for &l in c {
                let mut sad = 0;
                if variables[(l.abs() - 1) as usize] {
                    for &c in &p_clauses[(l.abs() - 1) as usize] {
                        if num_good_so_far[c] == 1 {
                            sad += 1;
                            if sad > min_sad {
                                break;
                            }
                        }
                    }
                } else {
                    for &c in &n_clauses[(l.abs() - 1) as usize] {
                        if num_good_so_far[c] == 1 {
                            sad += 1;
                            if sad > min_sad {
                                break;
                            }
                        }
                    }
                }
                if sad < min_sad {
                    min_sad = sad;
                    v_min_sad.clear();
                    v_min_sad.push((l.abs() - 1) as usize);
                } else if sad == min_sad {
                    v_min_sad.push((l.abs() - 1) as usize);
                }
            }

            let v = if min_sad == 0 {
                if v_min_sad.len() == 1 {
                    v_min_sad[0]
                } else {
                    v_min_sad[rng.gen_range(0..v_min_sad.len())]
                }
            } else {
                if rng.gen_bool(0.5) {
                    let l = c[rng.gen_range(0..c.len())];
                    (l.abs() - 1) as usize
                } else {
                    v_min_sad[rng.gen_range(0..v_min_sad.len())]
                }
            };

            if variables[v] {
                for &c in &n_clauses[v] {
                    num_good_so_far[c] += 1;
                    if num_good_so_far[c] == 1 {
                        residual.remove(&c);
                    }
                }
                for &c in &p_clauses[v] {
                    if num_good_so_far[c] == 1 {
                        residual.insert(c);
                    }
                    num_good_so_far[c] -= 1;
                }
            } else {
                for &c in &n_clauses[v] {
                    if num_good_so_far[c] == 1 {
                        residual.insert(c);
                    }
                    num_good_so_far[c] -= 1;
                }
                for &c in &p_clauses[v] {
                    num_good_so_far[c] += 1;
                    if num_good_so_far[c] == 1 {
                        residual.remove(&c);
                    }
                }
            }
            variables[v] = !variables[v];
        } else {
            break;
        }
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

    // Set KERNEL to None if algorithm only has a CPU implementation
    pub const KERNEL: Option<CudaKernel> = None;

    // Important! Your GPU and CPU version of the algorithm should return the same result
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