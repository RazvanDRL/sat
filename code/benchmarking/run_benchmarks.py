import sys
import os
import time
import glob
import argparse
import matplotlib.pyplot as plt
import numpy as np
from collections import defaultdict
from tabulate import tabulate

# Add the parent directory to the path
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# Import complete solvers
from dpll_solver.dpll import DPLLSolver
from resolution_prover.resolution import ResolutionProver
from dp_solver.dp import DPSolver
from cdcl_solver.cdcl import CDCLSolver

# Import incomplete solvers
from gsat_solver.gsat import GSATSolver
from walksat_solver.walksat import WalkSATSolver
from simulated_annealing_solver.simulated_annealing import SimulatedAnnealingSolver

from common.dimacs_parser import parse_dimacs_cnf

def run_solver(solver_name, solver_instance, clauses, num_vars, timeout=300):
    """Run a solver on a given instance and return results."""
    start_time = time.time()
    
    try:
        # Set a timeout for the solver execution
        import signal
        
        def timeout_handler(signum, frame):
            raise TimeoutError(f"Solver execution timed out after {timeout} seconds")
        
        # Set up the timeout
        original_handler = signal.signal(signal.SIGALRM, timeout_handler)
        signal.alarm(timeout)
        
        try:
            # Complete solvers
            if solver_name == "Resolution":
                satisfiable, _ = solver_instance.solve(clauses)
                assignment = None  # Resolution doesn't produce an assignment
            elif solver_name == "DPLL":
                satisfiable, assignment = solver_instance.solve(clauses, num_vars)
            elif solver_name == "DP" or solver_name == "CDCL":
                satisfiable, assignment = solver_instance.solve(clauses)
            # Incomplete solvers
            elif solver_name == "GSAT":
                satisfiable, assignment = solver_instance.solve()
            elif solver_name == "WalkSAT":
                satisfiable, assignment = solver_instance.solve()
            elif solver_name == "SimulatedAnnealing":
                satisfiable, assignment = solver_instance.solve()
            else:
                # Generic case - try common interface
                satisfiable, assignment = solver_instance.solve()
        finally:
            # Restore the original signal handler and cancel the alarm
            signal.signal(signal.SIGALRM, original_handler)
            signal.alarm(0)
        
        elapsed_time = time.time() - start_time
        
        return {
            "satisfiable": satisfiable,
            "time": elapsed_time,
            "stats": solver_instance.get_stats() if hasattr(solver_instance, 'get_stats') else {},
            "assignment": assignment
        }
    except TimeoutError as e:
        print(f"    Timeout: {solver_name} timed out after {timeout} seconds")
        return {
            "satisfiable": None,
            "time": timeout,
            "stats": solver_instance.get_stats() if hasattr(solver_instance, 'get_stats') else {},
            "error": str(e),
            "timeout": True
        }
    except Exception as e:
        print(f"Error running {solver_name}: {e}")
        return {
            "satisfiable": None,
            "time": time.time() - start_time,
            "stats": solver_instance.get_stats() if hasattr(solver_instance, 'get_stats') else {},
            "error": str(e)
        }

def run_benchmarks(cnf_files, solvers, heuristics=None, timeout=10):
    """
    Run benchmarks on all specified CNF files using the given solvers.
    Returns structured results.
    """
    if heuristics is None:
        heuristics = ["first_unassigned"]  # Default heuristic for DPLL
    
    results = {}
    
    for cnf_file in cnf_files:
        file_basename = os.path.basename(cnf_file)
        print(f"\nRunning benchmarks on {file_basename}...")
        
        try:
            clauses, num_vars, _ = parse_dimacs_cnf(cnf_file)
            results[file_basename] = {}
            
            print(f"  Formula has {num_vars} variables and {len(clauses)} clauses")
            
            # Run complete solvers
            # Run Resolution
            if "Resolution" in solvers:
                print(f"  Running Resolution...")
                prover = ResolutionProver()
                results[file_basename]["Resolution"] = run_solver("Resolution", prover, clauses, num_vars, timeout)
                if "timeout" in results[file_basename]["Resolution"]:
                    print(f"    Result: TIMEOUT")
                else:
                    print(f"    Result: {'UNSAT' if not results[file_basename]['Resolution']['satisfiable'] else 'Potentially SAT'}")
                print(f"    Time: {results[file_basename]['Resolution']['time']:.6f} seconds")
            
            # Run DP
            if "DP" in solvers:
                print(f"  Running Davis-Putnam...")
                dp_solver = DPSolver()
                results[file_basename]["DP"] = run_solver("DP", dp_solver, clauses, num_vars, timeout)
                if "timeout" in results[file_basename]["DP"]:
                    print(f"    Result: TIMEOUT")
                else:
                    print(f"    Result: {'SAT' if results[file_basename]['DP']['satisfiable'] else 'UNSAT'}")
                print(f"    Time: {results[file_basename]['DP']['time']:.6f} seconds")
            
            # Run DPLL with different heuristics
            if "DPLL" in solvers:
                for heuristic in heuristics:
                    print(f"  Running DPLL with {heuristic} heuristic...")
                    dpll_solver = DPLLSolver(heuristic)
                    solver_key = f"DPLL_{heuristic}"
                    results[file_basename][solver_key] = run_solver("DPLL", dpll_solver, clauses, num_vars, timeout)
                    if "timeout" in results[file_basename][solver_key]:
                        print(f"    Result: TIMEOUT")
                    else:
                        print(f"    Result: {'SAT' if results[file_basename][solver_key]['satisfiable'] else 'UNSAT'}")
                    print(f"    Time: {results[file_basename][solver_key]['time']:.6f} seconds")
            
            # Run CDCL
            if "CDCL" in solvers:
                print(f"  Running CDCL...")
                try:
                    cdcl_solver = CDCLSolver(clauses, num_vars)
                    results[file_basename]["CDCL"] = run_solver("CDCL", cdcl_solver, clauses, num_vars, timeout)
                    if "timeout" in results[file_basename]["CDCL"]:
                        print(f"    Result: TIMEOUT")
                    else:
                        print(f"    Result: {'SAT' if results[file_basename]['CDCL']['satisfiable'] else 'UNSAT'}")
                    print(f"    Time: {results[file_basename]['CDCL']['time']:.6f} seconds")
                except Exception as e:
                    print(f"    Error running CDCL: {e}")
                    results[file_basename]["CDCL"] = {"error": str(e), "satisfiable": None, "time": 0, "stats": {}}
            
            # Run incomplete solvers
            # Run GSAT
            if "GSAT" in solvers:
                print(f"  Running GSAT...")
                max_flips = 10000
                max_tries = 100
                gsat_solver = GSATSolver(clauses, num_vars, max_flips, max_tries)
                results[file_basename]["GSAT"] = run_solver("GSAT", gsat_solver, clauses, num_vars, timeout)
                if "timeout" in results[file_basename]["GSAT"]:
                    print(f"    Result: TIMEOUT")
                else:
                    print(f"    Result: {'SAT' if results[file_basename]['GSAT']['satisfiable'] else 'NO SOLUTION'}")
                print(f"    Time: {results[file_basename]['GSAT']['time']:.6f} seconds")
            
            # Run WalkSAT
            if "WalkSAT" in solvers:
                print(f"  Running WalkSAT...")
                max_flips = 10000
                max_tries = 100
                noise = 0.5
                walksat_solver = WalkSATSolver(clauses, num_vars, max_flips, max_tries, noise)
                results[file_basename]["WalkSAT"] = run_solver("WalkSAT", walksat_solver, clauses, num_vars, timeout)
                if "timeout" in results[file_basename]["WalkSAT"]:
                    print(f"    Result: TIMEOUT")
                else:
                    print(f"    Result: {'SAT' if results[file_basename]['WalkSAT']['satisfiable'] else 'NO SOLUTION'}")
                print(f"    Time: {results[file_basename]['WalkSAT']['time']:.6f} seconds")
            
            # Run Simulated Annealing
            if "SimulatedAnnealing" in solvers:
                print(f"  Running Simulated Annealing...")
                initial_temp = 2.0
                cooling_rate = 0.95
                steps_per_temp = 100
                sa_solver = SimulatedAnnealingSolver(clauses, num_vars, initial_temp, cooling_rate, steps_per_temp)
                results[file_basename]["SimulatedAnnealing"] = run_solver("SimulatedAnnealing", sa_solver, clauses, num_vars, timeout)
                if "timeout" in results[file_basename]["SimulatedAnnealing"]:
                    print(f"    Result: TIMEOUT")
                else:
                    print(f"    Result: {'SAT' if results[file_basename]['SimulatedAnnealing']['satisfiable'] else 'NO SOLUTION'}")
                print(f"    Time: {results[file_basename]['SimulatedAnnealing']['time']:.6f} seconds")
            
        except Exception as e:
            print(f"Error processing {file_basename}: {e}")
            results[file_basename] = {"error": str(e)}
    
    return results

def generate_tables(results):
    """Generate and print tables from benchmark results."""
    # Get all solver names first to avoid KeyError
    all_solvers = set()
    for file_result in results.values():
        all_solvers.update(file_result.keys())
    
    # Ensure at least one solver has valid results
    valid_results = False
    for file_result in results.values():
        for solver in all_solvers:
            if solver in file_result and "error" not in file_result[solver]:
                valid_results = True
                break
        if valid_results:
            break
    
    if not valid_results:
        print("No valid results to display.")
        return
    
    # Table 1: Solving time comparison
    time_data = []
    
    for filename, file_results in results.items():
        row = [filename]
        for solver_name in all_solvers:
            if solver_name in file_results and "error" not in file_results[solver_name]:
                row.append(f"{file_results[solver_name]['time']:.6f}s")
            else:
                row.append("ERROR")
        time_data.append(row)
    
    headers = ["Instance"] + list(all_solvers)
    print("\nTable 1: Solving Time Comparison (seconds)")
    print(tabulate(time_data, headers=headers, tablefmt="grid"))
    
    # Table 2: Satisfiability results
    sat_data = []
    
    for filename, file_results in results.items():
        row = [filename]
        for solver_name in all_solvers:
            if solver_name in file_results and "error" not in file_results[solver_name]:
                if file_results[solver_name]["satisfiable"] is None:
                    row.append("ERROR")
                elif solver_name == "Resolution" and file_results[solver_name]["satisfiable"]:
                    row.append("POTENTIALLY SAT")
                elif solver_name in ["GSAT", "WalkSAT", "SimulatedAnnealing"] and not file_results[solver_name]["satisfiable"]:
                    row.append("NO SOL")  # Incomplete solvers cannot prove UNSAT
                else:
                    row.append("SAT" if file_results[solver_name]["satisfiable"] else "UNSAT")
            else:
                row.append("ERROR")
        sat_data.append(row)
    
    print("\nTable 2: Satisfiability Results")
    print(tabulate(sat_data, headers=headers, tablefmt="grid"))
    
    # Table 3: Algorithm-specific metrics for complete solvers
    for solver_type in ["DPLL", "DP", "Resolution", "CDCL"]:
        print(f"\nTable 3a: {solver_type} Specific Metrics")
        
        for filename, file_results in results.items():
            metrics_data = []
            metrics_headers = ["Metric"]
            
            # Collect all solver variants of this type
            solver_variants = [solver for solver in file_results.keys() if solver.startswith(solver_type)]
            metrics_headers.extend(solver_variants)
            
            if not solver_variants:
                continue
                
            # Check if there's at least one solver with valid results
            valid_solver = False
            for solver in solver_variants:
                if "error" not in file_results[solver]:
                    valid_solver = True
                    break
            
            if not valid_solver:
                continue
                
            # Get all metrics from the first valid solver variant
            metrics = set()
            for solver in solver_variants:
                if "error" not in file_results[solver]:
                    metrics.update(file_results[solver]["stats"].keys())
                    break
            
            if not metrics:
                continue
                
            for metric in metrics:
                row = [metric]
                for solver in solver_variants:
                    if "error" not in file_results[solver]:
                        row.append(file_results[solver]["stats"].get(metric, "N/A"))
                    else:
                        row.append("ERROR")
                metrics_data.append(row)
            
            print(f"\nInstance: {filename}")
            print(tabulate(metrics_data, headers=metrics_headers, tablefmt="grid"))
    
    # Table 3b: Algorithm-specific metrics for incomplete solvers
    for solver_type in ["GSAT", "WalkSAT", "SimulatedAnnealing"]:
        if any(solver_type in file_results and "error" not in file_results[solver_type] for file_results in results.values()):
            print(f"\nTable 3b: {solver_type} Specific Metrics")
            
            for filename, file_results in results.items():
                if solver_type not in file_results or "error" in file_results[solver_type]:
                    continue
                    
                metrics_data = []
                metrics_headers = ["Metric", solver_type]
                
                metrics = file_results[solver_type]["stats"].keys()
                
                for metric in metrics:
                    row = [metric, file_results[solver_type]["stats"].get(metric, "N/A")]
                    metrics_data.append(row)
                
                print(f"\nInstance: {filename}")
                print(tabulate(metrics_data, headers=metrics_headers, tablefmt="grid"))

def generate_plots(results, output_dir="plots"):
    """Generate comparison plots from benchmark results."""
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    
    # Get all solver types
    all_solvers = set()
    for file_results in results.values():
        all_solvers.update(file_results.keys())
    all_solvers = sorted(list(all_solvers))
    
    # Plot 1: Solving time comparison
    plt.figure(figsize=(12, 8))
    
    bar_width = 0.8 / len(all_solvers)
    index = np.arange(len(results))
    
    for i, solver in enumerate(all_solvers):
        times = []
        for file_results in results.values():
            if solver in file_results and "error" not in file_results[solver]:
                times.append(file_results[solver]["time"])
            else:
                times.append(0)  # Placeholder for missing/error data
        
        plt.bar(index + i * bar_width, times, bar_width, label=solver)
    
    plt.xlabel("Instance")
    plt.ylabel("Time (seconds)")
    plt.title("SAT Solver Performance Comparison")
    plt.xticks(index + bar_width * (len(all_solvers) - 1) / 2, list(results.keys()), rotation=45)
    plt.legend(loc="best")
    plt.tight_layout()
    plt.savefig(os.path.join(output_dir, "solving_time_comparison.png"))
    
    # Plot 2: DPLL heuristics comparison (if applicable)
    dpll_solvers = [solver for solver in all_solvers if solver.startswith("DPLL")]
    if len(dpll_solvers) > 1:
        plt.figure(figsize=(12, 8))
        
        bar_width = 0.8 / len(dpll_solvers)
        index = np.arange(len(results))
        
        for i, solver in enumerate(dpll_solvers):
            times = []
            for file_results in results.values():
                if solver in file_results and "error" not in file_results[solver]:
                    times.append(file_results[solver]["time"])
                else:
                    times.append(0)  # Placeholder for missing/error data
            
            plt.bar(index + i * bar_width, times, bar_width, label=solver)
        
        plt.xlabel("Instance")
        plt.ylabel("Time (seconds)")
        plt.title("DPLL Heuristics Comparison")
        plt.xticks(index + bar_width * (len(dpll_solvers) - 1) / 2, list(results.keys()), rotation=45)
        plt.legend(loc="best")
        plt.tight_layout()
        plt.savefig(os.path.join(output_dir, "dpll_heuristics_comparison.png"))

def main():
    parser = argparse.ArgumentParser(description="Run SAT solver benchmarks")
    parser.add_argument("--files", nargs="*", default=None, help="Specific CNF files to run (default: all in test_data)")
    parser.add_argument("--solvers", nargs="*", 
                        choices=["DPLL", "DP", "Resolution", "CDCL", "GSAT", "WalkSAT", "SimulatedAnnealing"], 
                        default=["DPLL", "DP", "Resolution", "CDCL", "GSAT", "WalkSAT", "SimulatedAnnealing"], 
                        help="Solvers to run")
    parser.add_argument("--heuristics", nargs="*", default=["first_unassigned", "random_unassigned"], 
                        help="Heuristics for DPLL")
    parser.add_argument("--type", choices=["complete", "incomplete", "all"], default="all",
                       help="Type of solvers to run (complete, incomplete, or all)")
    parser.add_argument("--timeout", type=int, default=10, help="Timeout in seconds for each solver run")
    
    args = parser.parse_args()
    
    # Filter solvers by type if specified
    if args.type == "complete":
        args.solvers = [s for s in args.solvers if s in ["DPLL", "DP", "Resolution", "CDCL"]]
    elif args.type == "incomplete":
        args.solvers = [s for s in args.solvers if s in ["GSAT", "WalkSAT", "SimulatedAnnealing"]]
    
    # Get CNF files
    if args.files:
        cnf_files = args.files
    else:
        cnf_files = glob.glob(os.path.join(os.path.dirname(__file__), "test_data", "*.cnf"))
    
    if not cnf_files:
        print("No CNF files found.")
        return
    
    # Run benchmarks
    results = run_benchmarks(cnf_files, args.solvers, args.heuristics, args.timeout)
    
    # Generate tables and plots
    generate_tables(results)
    generate_plots(results)
    
    print("\nBenchmarking complete. Check the 'plots' directory for visualizations.")

if __name__ == "__main__":
    main() 