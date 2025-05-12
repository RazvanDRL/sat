# Compararea algoritmilor SAT

Acest repo conține implementări în Python ale algoritmilor de rezolvare a satisfiabilității booleene (SAT), împreună cu un cod de benchmarking pentru compararea lor.

## Algoritmi implementați

1. **Algoritmi compleți**:
   - **Resolution** – O metodă pentru a demonstra nesatisfiabilitatea prin derivarea clauzei goale
   - **Davis-Putnam (DP)** – Abordarea originală bazată pe eliminarea variabilelor
   - **Davis-Putnam-Logemann-Loveland (DPLL)** – Un algoritm de backtracking cu propagare unitară
   - **Conflict-Driven Clause Learning (CDCL)** – Extensie modernă a DPLL cu analiză a conflictelor și backtracking necronologic

2. **Algoritmi incompleți**:
   - **GSAT** – Un algoritm de căutare locală lacomă pentru probleme SAT
   - **WalkSAT** – Extensie a GSAT cu plimbări aleatorii pentru a evita optimele locale
   - **Simulated Annealing** – O chestiune care permite acceptarea soluțiilor mai slabe cu probabilitate descrescătoare

## Structura proiectului

```text
code/
├── common/                     # Utilitare comune partajate între soluționatori
│   ├── structures.py           # Structuri de date pentru literali și atribuiri
│   └── dimacs_parser.py        # Analizor (parser) pentru formatul DIMACS CNF
│
├── dpll_solver/                # Implementarea algoritmului DPLL
│   ├── dpll.py                 # Clasa principală a soluționatorului DPLL
│   └── heuristics.py           # Diferite euristici de selecție a variabilelor
│
├── resolution_prover/          # Implementarea metodei Resolution
│   └── resolution.py           # Prover bazat pe rezoluție
│
├── dp_solver/                  # Implementarea algoritmului Davis-Putnam
│   └── dp.py                   # Soluționator DP folosind eliminarea variabilelor
│
├── cdcl_solver/                # Soluționator CDCL cu watched literals și VSIDS
│   └── cdcl.py                 # Soluționator CDCL cu watched literals și VSIDS
│
├── gsat_solver/                # Implementarea algoritmului GSAT
│   └── gsat.py                 # Soluționator GSAT (căutare locală stocastică)
│
├── walksat_solver/             # Implementarea algoritmului WalkSAT
│   └── walksat.py              # Soluționator WalkSAT (cu parametrul de zgomot)
│
├── simulated_annealing_solver/ # Implementarea Simulated Annealing pentru SAT
│   └── simulated_annealing.py  # Soluționator Simulated Annealing
│
├── benchmarking/               # Cadrul de benchmarking
│   ├── run_benchmarks.py       # Script pentru rularea și compararea tuturor soluționatorilor
│   └── test_data/              # Instanțe CNF de exemplu pentru testare
│       ├── simple_sat.cnf      # O instanță simplă satisfiabilă
│       ├── simple_unsat.cnf    # O instanță simplă nesatisfiabilă
│       ├── medium_sat.cnf      # O instanță de dimensiuni medii satisfiabilă
│       └── difficult_unsat.cnf # O instanță dificilă nesatisfiabilă (principiul sertarului)
│
├── plots/                      # Director pentru graficele rezultatelor benchmark-urilor
│
└── README.md                   # Acest fișier
```

## Cerințe

Codul necesită Python 3.6+ și următoarele pachete:
- numpy
- matplotlib
- tabulate

Poți instala aceste dependențe cu:

```bash
pip install numpy matplotlib tabulate
```

## Utilizare

### Rularea soluționatorilor individuali

Fiecare soluționator poate fi rulat direct pe fișiere DIMACS CNF:

```bash
# Algoritmi compleți

# Rulează soluționatorul DPLL cu euristica implicită first_unassigned
python -m dpll_solver.dpll benchmarking/test_data/simple_sat.cnf

# Rulează soluționatorul DPLL cu euristica random_unassigned
python -m dpll_solver.dpll benchmarking/test_data/simple_sat.cnf random_unassigned

# Rulează soluționatorul Davis-Putnam
python -m dp_solver.dp benchmarking/test_data/simple_sat.cnf

# Rulează prover-ul Resolution
python -m resolution_prover.resolution benchmarking/test_data/simple_unsat.cnf

# Rulează soluționatorul CDCL
python -m cdcl_solver.cdcl benchmarking/test_data/simple_sat.cnf

# Algoritmi incompleți

# Rulează soluționatorul GSAT
python -m gsat_solver.gsat benchmarking/test_data/simple_sat.cnf 100000 100

# Rulează soluționatorul WalkSAT (cu parametrul de zgomot 0.5)
python -m walksat_solver.walksat benchmarking/test_data/simple_sat.cnf 100000 100 0.5

# Rulează soluționatorul Simulated Annealing
python -m simulated_annealing_solver.simulated_annealing benchmarking/test_data/simple_sat.cnf 2.0 0.95 100
```

### Rularea benchmark-urilor

Scriptul de benchmarking compară toate metodele de soluționare.

```bash
# Rulează benchmark-uri cu toate metodele de soluționare
python -m benchmarking.run_benchmarks

# Rulează doar metodele de soluționare specificate
python -m benchmarking.run_benchmarks --solvers DPLL CDCL GSAT WalkSAT

# Rulează doar metodele de soluționare complete
python -m benchmarking.run_benchmarks --type complete

# Rulează doar metodele de soluționare incomplete
python -m benchmarking.run_benchmarks --type incomplete

# Rulează cu euristici specifice pentru DPLL
python -m benchmarking.run_benchmarks --heuristics first_unassigned random_unassigned

# Rulează pe fișiere CNF specifice
python -m benchmarking.run_benchmarks --files path/to/file1.cnf path/to/file2.cnf
```

Rezultatele benchmark-urilor vor fi afișate în tabele și salvate ca grafice în folderul `plots`.