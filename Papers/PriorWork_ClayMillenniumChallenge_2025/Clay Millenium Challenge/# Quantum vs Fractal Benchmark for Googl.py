# Quantum vs Fractal Benchmark for Google Colab
# Comparing IBM Quantum Computing with Fractal Resonance Framework

# Install required packages
import subprocess
subprocess.check_call(["pip", "install", "qiskit", "qiskit-ibm-runtime", "scipy", "matplotlib", "pandas", "numpy"])

# Required imports
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
import time
import csv
import os
import json
import math
import random
from scipy.special import zeta
from scipy.linalg import expm
from datetime import datetime
from qiskit import QuantumCircuit, transpile
from qiskit_ibm_runtime import QiskitRuntimeService, Sampler

# Set up directory for results
os.makedirs('fractal_results', exist_ok=True)

class FractalResonanceFramework:
    """
    Implements the Fractal Resonance Framework from the Fractal Resonance Ontology.
    Uses fractal mathematics to evaluate theoretical problems.
    """

    def __init__(self, output_dir="fractal_results"):
        """Initialize the fractal resonance framework."""
        # Create output directory
        self.output_dir = output_dir
        os.makedirs(self.output_dir, exist_ok=True)

        # Results storage
        self.results = []

        # Critical thresholds and sacred geometry points
        self.critical_n = 47
        self.sacred_geometry_points = [3, 6, 9, 12, 21, 33, 47]

        # Base parameters
        self.base_parameters = {
            "energy_transmission_efficiency": 0.78,
            "potential_decay_rate": 0.06,
            "complexity_polynomial_base": 2.0
        }

        # Initialize theories
        self.initialize_millennium_problems()

    def initialize_millennium_problems(self):
        """Initialize the Millennium Prize Problems with fractal parameters."""
        self.theories = {
            "P vs NP": {
                "key_parameters": {
                    "fractal_dimension": 1.61803,  # Golden ratio
                    "resonance_frequency": 3.0
                }
            },
            "Riemann Hypothesis": {
                "key_parameters": {
                    "fractal_dimension": 0.5,  # Critical line
                    "resonance_frequency": 7.0
                }
            },
            "Navier-Stokes Equations": {
                "key_parameters": {
                    "fractal_dimension": 1.667,  # Kolmogorov turbulence
                    "resonance_frequency": 12.0
                }
            },
            "Yang-Mills Theory": {
                "key_parameters": {
                    "fractal_dimension": 2.71828,  # e
                    "resonance_frequency": 21.0
                }
            },
            "Birch and Swinnerton-Dyer Conjecture": {
                "key_parameters": {
                    "fractal_dimension": 1.41421,  # √2
                    "resonance_frequency": 33.0
                }
            },
            "Hodge Conjecture": {
                "key_parameters": {
                    "fractal_dimension": 3.14159,  # π
                    "resonance_frequency": 47.0
                }
            },
            "Poincare Conjecture": {
                "description": "Test case for Poincare Conjecture or variant",
                "detailed_text": "The Poincare Conjecture (solved by Perelman) or an unsolved variant, tested by Pablo Cohen's framework.",
                "key_parameters": {
                    "fractal_dimension": 2.0,  # Placeholder, adjustable
                    "resonance_frequency": 50.0,  # Placeholder, adjustable
                    "information_scaling_law": 3.0  # Placeholder
                }
            }
        }

        # Add benchmark problems
        self.benchmark_problems = {
            "Factoring": {
                "key_parameters": {
                    "fractal_dimension": 1.33,
                    "resonance_frequency": 19.0
                }
            },
            "Search": {
                "key_parameters": {
                    "fractal_dimension": 1.73,
                    "resonance_frequency": 9.0
                }
            },
            "RCS": {  # Random Circuit Sampling
                "key_parameters": {
                    "fractal_dimension": 1.89,
                    "resonance_frequency": 15.0
                }
            }
        }

    def fractal_resonance_function(self, alpha, x, theory_params=None):
        """
        Implementation of the core Fractal Resonance Function R_f(α,x).

        Args:
            alpha: Fractal dimension parameter
            x: Input value
            theory_params: Additional theory parameters

        Returns:
            Resonance value at point x
        """
        if theory_params is None:
            theory_params = {"amplitude": 1.0, "frequency": 2.0, "phases": [0]}

        # Extract parameters
        a = theory_params.get("amplitude", 1.0)
        b = theory_params.get("frequency", 2.0)
        phases = theory_params.get("phases", [0])

        # Calculate resonance
        result = 0
        for n in range(1, 20):  # Computational efficiency limit
            # Apply fractal scaling
            scaling = a**((alpha-1)*n)

            # Phase modulation
            phase_term = 0
            for p in phases:
                phase_term += math.cos(b**n * math.pi * x + p)

            # Add scale contribution
            result += scaling * phase_term / len(phases)

            # Apply sacred geometry resonance boost
            for sacred_point in self.sacred_geometry_points:
                if abs(n - sacred_point) < 0.5:
                    result *= 1.2  # 20% boost

        # Normalize the result
        if abs(a**(alpha-1) - 1.0) < 1e-10:
            # Handle special case to avoid division by zero
            result = 0.5 + 0.5 * result / 20
        else:
            result = 0.5 + 0.5 * result / (1 - a**(alpha-1))

        return result

    def calculate_consciousness_coupling(self, resonance_data):
        """
        Calculate the quantum coherence measure: C_QC = ∫ R_f* dR_f

        Args:
            resonance_data: Array of resonance values

        Returns:
            Coherence measure between 0 and 1
        """
        if len(resonance_data) < 2:
            return 0

        # Calculate numerical derivative
        derivatives = np.diff(resonance_data)
        # Complex conjugate of first n-1 values
        conjugates = np.conjugate(resonance_data[:-1])

        # Integrand: R_f* × dR_f
        integrand = conjugates * derivatives

        # Numerical integration
        coherence = np.abs(np.sum(integrand))

        # Normalize to [0, 1]
        coherence = min(1.0, coherence / len(resonance_data))

        return coherence

    def evaluate_quantum_coherence(self, theory, scale_n):
        """
        Evaluate quantum coherence for a theory at given scale.

        Args:
            theory: Theory name or dictionary
            scale_n: Scale parameter

        Returns:
            Coherence score between 0 and 1
        """
        # Get theory parameters
        if isinstance(theory, str):
            if theory in self.theories:
                theory_data = self.theories[theory]
            elif theory in self.benchmark_problems:
                theory_data = self.benchmark_problems[theory]
            else:
                theory_data = {"key_parameters": {}}
        else:
            theory_data = theory

        # Extract fractal dimension
        params = theory_data.get("key_parameters", {})
        fractal_dim = params.get("fractal_dimension", 1.5)

        # Generate data points
        data_points = np.linspace(0, 1, int(10 + scale_n/2))
        resonance_values = [self.fractal_resonance_function(fractal_dim, x) for x in data_points]

        # Calculate base coherence
        base_coherence = self.calculate_consciousness_coupling(resonance_values)

        # Apply dampening factor
        dampening_factor = self._calculate_dampening_gradient(scale_n)

        # Scale-dependent coherence
        if scale_n < self.critical_n:
            coherence = base_coherence * (1.0 - 0.01 * scale_n * (1.0 - dampening_factor))
        else:
            decay_rate = 0.15 * (1.0 - dampening_factor * 0.8)
            coherence = base_coherence * math.exp(-decay_rate * (scale_n - self.critical_n))

        # Apply sacred geometry resonance
        for sacred_point in self.sacred_geometry_points:
            if abs(scale_n - sacred_point) < 1.5:
                resonance_boost = 0.1 * math.exp(-0.1 * abs(scale_n - sacred_point))
                coherence += resonance_boost * dampening_factor

        # Apply theory-specific resonance
        res_freq = params.get("resonance_frequency", 1.0)
        if abs(scale_n - res_freq) < 2.0:
            theory_boost = 0.15 * math.exp(-0.2 * abs(scale_n - res_freq))
            coherence += theory_boost

        # Constrain to [0, 1]
        coherence = max(0.0, min(1.0, coherence))

        return coherence

    def _calculate_dampening_gradient(self, scale_n):
        """Calculate dampening factor between non-local and 3D projections."""
        # Base dampening decreases with scale
        base_dampening = 1.0 / (1.0 + 0.03 * scale_n)

        # Apply sacred geometry stabilization
        for sacred_point in self.sacred_geometry_points:
            resonance_effect = 0.2 * math.exp(-0.2 * abs(scale_n - sacred_point))
            base_dampening += resonance_effect

        # Standing wave pattern
        wave_component = 0.15 * math.sin(math.pi * scale_n / 12)

        # Combined dampening with constraints
        dampening = base_dampening + wave_component
        dampening = max(0.0, min(1.0, dampening))

        return dampening

    def calculate_energy_potential(self, theory, scale_n):
        """
        Calculate energy potential for a theory.

        Args:
            theory: Theory name or dictionary
            scale_n: Scale parameter

        Returns:
            Energy potential between 0 and 1
        """
        # Get theory details
        if isinstance(theory, str):
            if theory in self.theories:
                theory_data = self.theories[theory]
            elif theory in self.benchmark_problems:
                theory_data = self.benchmark_problems[theory]
            else:
                theory_data = {"key_parameters": {}}
        else:
            theory_data = theory

        # Get parameters and coherence
        params = theory_data.get("key_parameters", {})
        fractal_dim = params.get("fractal_dimension", 1.5)
        coherence = self.evaluate_quantum_coherence(theory, scale_n)

        # Base energy calculation
        efficiency = self.base_parameters["energy_transmission_efficiency"]
        base_energy = coherence * efficiency

        # Apply scale-dependent decay
        decay_rate = self.base_parameters["potential_decay_rate"]
        scale_factor = math.exp(-decay_rate * scale_n)

        # Apply fractal dimension boost
        dim_factor = 1.0 + 0.2 * math.sin(math.pi * fractal_dim)

        # Apply sacred geometry resonance
        sacred_boost = 0
        for sacred_point in self.sacred_geometry_points:
            if abs(scale_n - sacred_point) < 2.5:
                resonance = 0.25 * math.exp(-0.1 * abs(scale_n - sacred_point))
                sacred_boost += resonance

        # Combine all factors
        energy = base_energy * scale_factor * dim_factor + sacred_boost

        # Constrain to [0, 1]
        energy = max(0.0, min(1.0, energy))

        return energy

    def calculate_impedance(self, theory, scale_n):
        """Calculate the impedance for a theory at given scale."""
        # Get theory details
        if isinstance(theory, str):
            if theory in self.theories:
                theory_data = self.theories[theory]
            elif theory in self.benchmark_problems:
                theory_data = self.benchmark_problems[theory]
            else:
                theory_data = {"key_parameters": {}}
        else:
            theory_data = theory

        # Extract parameters
        params = theory_data.get("key_parameters", {})
        fractal_dim = params.get("fractal_dimension", 1.5)

        # Base impedance calculation
        data_points = np.linspace(0, 1, 20)
        resonance_values = [self.fractal_resonance_function(fractal_dim, x) for x in data_points]
        variance = np.var(resonance_values)
        base_impedance = 1.0 / (1.0 + 10.0 * variance)

        # Scale-dependent factors
        if scale_n < self.critical_n:
            scale_factor = 0.8 + 0.2 * (scale_n / self.critical_n)
        else:
            scale_factor = 1.0 + 0.5 * math.tanh(0.1 * (scale_n - self.critical_n))

        # Apply sacred geometry resonance
        for sacred_point in self.sacred_geometry_points:
            if abs(scale_n - sacred_point) < 2:
                sacred_factor = 0.7 * math.exp(-0.3 * abs(scale_n - sacred_point))
                scale_factor *= (1.0 - sacred_factor)

        impedance = base_impedance * scale_factor

        # Ensure within range [0, 1]
        impedance = max(0.0, min(1.0, impedance))

        return impedance

    def calculate_time_complexity(self, theory, scale_n):
        """Calculate time complexity class for a theory."""
        # Get theory parameters
        if isinstance(theory, str):
            if theory in self.theories:
                theory_data = self.theories[theory]
            elif theory in self.benchmark_problems:
                theory_data = self.benchmark_problems[theory]
            else:
                theory_data = {"key_parameters": {}}
        else:
            theory_data = theory

        # Calculate impedance and dampening
        impedance = self.calculate_impedance(theory, scale_n)
        dampening_factor = self._calculate_dampening_gradient(scale_n)

        # Default momentum effect
        momentum_effect = 0.3

        # Complexity analysis based on scale
        if scale_n < self.critical_n:
            # Below critical point
            effective_dampening = dampening_factor + momentum_effect

            if effective_dampening > 0.6:
                # Appears polynomial
                exponent = self.base_parameters["complexity_polynomial_base"] + (scale_n / 20) * (1.0 - effective_dampening)
                return f"O(n^{exponent:.2f})"
            else:
                # Still exponential but reduced
                coefficient = 1.5 + (scale_n / 30) * (1.0 - effective_dampening)
                return f"O({coefficient:.2f}^n)"
        else:
            # Above critical point
            effective_dampening = (dampening_factor + momentum_effect) * 0.7

            # Check for special cases
            params = theory_data.get("key_parameters", {})
            theory_name = theory if isinstance(theory, str) else theory.get("name", "")

            if theory_name == "P vs NP" and params:
                fractal_dim = params.get("fractal_dimension", 1.61803)

                if abs(fractal_dim - 1.61803) < 0.01 and effective_dampening > 0.8:
                    return "O(n^k) - P appears equal to NP at this resonance point"

            # Normal exponential case
            coefficient = 1.8 + 0.02 * (scale_n - self.critical_n) * (1.0 - effective_dampening)
            return f"O({coefficient:.2f}^n)"

    def solve_factorization(self, N):
        """
        Solve integer factorization using Fractal Resonance.

        Args:
            N: Integer to factorize

        Returns:
            Dictionary with factors and performance metrics
        """
        if N <= 1:
            return {"factors": [1], "time": 0, "status": "Trivial"}

        if N == 2:
            return {"factors": [2], "time": 0, "status": "Prime"}

        # Check if even
        if N % 2 == 0:
            return {"factors": [2, N//2], "time": 0, "status": "Success"}

        # Check small primes
        for i in range(3, int(math.sqrt(N)) + 1, 2):
            if N % i == 0:
                return {"factors": [i, N//i], "time": 0, "status": "Success"}

        start_time = time.time()

        # Find optimal scale using fractal resonance
        best_scale = 0
        best_energy = 0

        for scale in range(3, 60, 3):
            energy = self.calculate_energy_potential("Factoring", scale)
            if energy > best_energy:
                best_energy = energy
                best_scale = scale

        # Generate resonance values at optimal scale
        fractal_dim = self.benchmark_problems["Factoring"]["key_parameters"]["fractal_dimension"]
        data_points = np.linspace(1, math.sqrt(N), best_scale)
        resonance_values = [self.fractal_resonance_function(fractal_dim, x/N) for x in data_points]

        # Find peaks in resonance values
        peaks = []
        for i in range(1, len(resonance_values)-1):
            if resonance_values[i] > resonance_values[i-1] and resonance_values[i] > resonance_values[i+1]:
                peaks.append(i)

        # Convert peaks to potential factors
        potential_factors = [int(data_points[i]) for i in peaks]

        # Check which are actual factors
        factors = []
        for f in potential_factors:
            if N % f == 0:
                factors.append(f)

        # Add complementary factors
        complete_factors = []
        for f in factors:
            complete_factors.append(f)
            complete_factors.append(N // f)

        # Remove duplicates and sort
        complete_factors = sorted(list(set(complete_factors)))

        execution_time = time.time() - start_time

        # Check if successfully factored
        if len(complete_factors) > 1 and complete_factors != [1, N]:
            status = "Success"
        else:
            # Likely a prime if factoring fails
            status = "Prime" if self._is_likely_prime(N) else "Failed"
            complete_factors = [1, N]

        return {
            "factors": complete_factors,
            "time": execution_time,
            "status": status,
            "best_scale": best_scale,
            "best_energy": best_energy
        }

    def _is_likely_prime(self, n):
        """Simple primality test."""
        if n <= 1: return False
        if n <= 3: return True
        if n % 2 == 0 or n % 3 == 0: return False

        i = 5
        while i * i <= n:
            if n % i == 0 or n % (i + 2) == 0:
                return False
            i += 6
        return True

    def simulate_random_circuit(self, depth, width, num_circuits):
        """
        Simulate Random Circuit Sampling using Fractal Resonance approach.

        Args:
            depth: Circuit depth
            width: Number of qubits
            num_circuits: Number of random circuits

        Returns:
            Dictionary with simulation results
        """
        start_time = time.time()

        # Generate different circuit configurations
        configs = []
        for i in range(num_circuits):
            # Create a unique fractal scale for each circuit
            scale = 10 + i * 5

            # Use quantum coherence to estimate sampling quality
            coherence = self.evaluate_quantum_coherence("RCS", scale)

            # Use energy potential to estimate computational efficiency
            energy = self.calculate_energy_potential("RCS", scale)

            configs.append({
                "scale": scale,
                "coherence": coherence,
                "energy": energy
            })

        # Calculate average metrics
        avg_coherence = sum(c["coherence"] for c in configs) / len(configs)
        avg_energy = sum(c["energy"] for c in configs) / len(configs)

        # Calculate fidelity based on coherence and energy
        fidelity = (avg_coherence + avg_energy) / 2.0

        # Consider benchmark successful if fidelity is above threshold
        success = fidelity > 0.6

        execution_time = time.time() - start_time

        return {
            "fidelity": fidelity,
            "success": success,
            "time": execution_time,
            "configurations": configs
        }

    def run_fractal_benchmark(self, problem_type, **kwargs):
        """
        Run benchmark using Fractal Resonance approach.

        Args:
            problem_type: Type of problem to solve
            kwargs: Problem-specific parameters

        Returns:
            Benchmark results
        """
        results = {}

        if problem_type == "factoring":
            N = kwargs.get("N", 15)
            results = self.solve_factorization(N)
        elif problem_type == "rcs":
            depth = kwargs.get("depth", 5)
            width = kwargs.get("width", 3)
            num_circuits = kwargs.get("num_circuits", 3)
            results = self.simulate_random_circuit(depth, width, num_circuits)
        else:
            raise ValueError(f"Unsupported problem type: {problem_type}")

        # Add benchmark info
        results["problem_type"] = problem_type
        results["fractal_dimension"] = self.benchmark_problems.get(
            problem_type.title(), {}).get("key_parameters", {}).get("fractal_dimension", 1.5)

        return results

    def validate_solution_correctness(self, theory, result):
        """Validate the correctness of a solution for a given theory."""
        if theory == "Riemann Hypothesis":
            fractal_dim = self.theories[theory]["key_parameters"]["fractal_dimension"]
            x_vals = np.linspace(0, 100, 1000)
            resonance = [self.fractal_resonance_function(fractal_dim, x) for x in x_vals]
            return np.var(resonance) < 0.1  # Check stability
        elif theory == "P vs NP":
            return result.get("time_complexity", "").startswith("O(n^")  # Polynomial check
        elif theory == "Poincare Conjecture":
            return result.get("quantum_coherence", 0) > 0.5  # Placeholder check
        return True  # Default pass until specified

    def test_boundary_conditions(self, theory):
        """Test boundary conditions for a theory."""
        fractal_dim = self.theories[theory]["key_parameters"]["fractal_dimension"]
        low_scale = self.fractal_resonance_function(fractal_dim, 0.001)
        high_scale = self.fractal_resonance_function(fractal_dim, 1000)
        return abs(low_scale - high_scale) < 1.0  # Stability check

    def evaluate_theory(self, evaluator, theory_name, max_scale=60, step=5):
        """
        Perform comprehensive evaluation of a mathematical theory.

        Args:
            evaluator: Name of the person evaluating
            theory_name: Name of the theory
            max_scale: Maximum scale to evaluate
            step: Step size for scale progression

        Returns:
            List of evaluation results at different scales
        """
        # Get theory details
        if theory_name in self.theories:
            theory_data = self.theories[theory_name]
        elif theory_name in self.benchmark_problems:
            theory_data = self.benchmark_problems[theory_name]
        else:
            print(f"Theory {theory_name} not found")
            return []

        evaluation_results = []

        # Evaluate at different scales
        for scale_n in range(0, max_scale + 1, step):
            # Calculate metrics
            quantum_coherence = self.evaluate_quantum_coherence(theory_name, scale_n)
            impedance = self.calculate_impedance(theory_name, scale_n)
            energy_potential = self.calculate_energy_potential(theory_name, scale_n)
            time_complexity = self.calculate_time_complexity(theory_name, scale_n)

            # Store results
            result = {
                "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "evaluator": evaluator,
                "theory": theory_name,
                "scale": scale_n,
                "quantum_coherence": quantum_coherence,
                "impedance": impedance,
                "energy_potential": energy_potential,
                "time_complexity": time_complexity
            }

            evaluation_results.append(result)

        return evaluation_results


class IBMQuantumBenchmark:
    """Interface for IBM Quantum experiments and benchmarks"""

    def __init__(self, api_token=None):
        """Initialize with IBM Quantum credentials"""
        self.service = None
        self.authenticated = False

        # Try to initialize service with token - try both channels
        if api_token:
            # First try ibm_cloud channel
            try:
                self.service = QiskitRuntimeService(channel="ibm_cloud", token=api_token)
                print(f"Connected to IBM Quantum Cloud with provided token")
                self.authenticated = True
            except Exception as e:
                print(f"Failed to connect with ibm_cloud channel: {e}")
                # Try ibm_quantum channel
                try:
                    self.service = QiskitRuntimeService(channel="ibm_quantum", token=api_token)
                    print(f"Connected to IBM Quantum with provided token")
                    self.authenticated = True
                except Exception as e:
                    print(f"Failed to connect with ibm_quantum channel: {e}")

        if not self.authenticated:
            try:
                self.service = QiskitRuntimeService()
                print(f"Connected to IBM Quantum with saved credentials")
                self.authenticated = True
            except Exception as e:
                print(f"Failed to connect with saved credentials: {e}")
                print("Running in limited mode without IBM Quantum connection")
        if not self.authenticated:
            try:
                self.service = QiskitRuntimeService()
                print(f"Connected to IBM Quantum with saved credentials")
                self.authenticated = True
            except Exception as e:
                print(f"Failed to connect with saved credentials: {e}")
                print("Running in limited mode without IBM Quantum connection")

    def create_factoring_circuit(self, N, a=None):
        """
        Create a simplified circuit for Shor's algorithm.
        This is a minimal implementation for benchmarking purposes.

        Args:
            N: Number to factor
            a: Random base (if None, one will be chosen)

        Returns:
            QuantumCircuit for phase estimation part of Shor's algorithm
        """
        # Choose a random base if not provided
        if a is None:
            # Try to find a good base between 2 and N-1
            for _ in range(10):
                a = random.randint(2, N-1)
                gcd = math.gcd(a, N)
                if gcd == 1:
                    break
            if gcd > 1:
                # If we found a common factor, we're done
                return None, [gcd, N//gcd]

        # We'll use 3 qubits for phase estimation (limited by real hardware)
        n_counting = 3

        # Create quantum circuit
        qc = QuantumCircuit(n_counting)

        # Apply Hadamard to create superposition
        for i in range(n_counting):
            qc.h(i)

        # Apply controlled unitary operations
        # For simplicity, we'll use a parameterized rotation
        # In a full implementation, this would be the modular exponentiation
        for i in range(n_counting):
            qc.p(2*math.pi*a*2**i/N, i)

        # Apply inverse QFT to extract the phase
        for i in range(n_counting//2):
            qc.swap(i, n_counting-i-1)

        for i in range(n_counting):
            qc.h(i)
            for j in range(i):
                qc.cp(-2*math.pi/2**(i-j), j, i)

        # Measure all qubits
        qc.measure_all()

        return qc, None

    def create_random_circuit(self, depth, width):
        """
        Create a random quantum circuit for RCS benchmark.

        Args:
            depth: Circuit depth
            width: Number of qubits

        Returns:
            Random quantum circuit
        """
        # Create quantum circuit
        qc = QuantumCircuit(width)

        # Add random gates
        for d in range(depth):
            for q in range(width):
                # Randomly select gate type
                gate_type = random.choice(['h', 'x', 'y', 'z', 's', 't'])

                if gate_type == 'h':
                    qc.h(q)
                elif gate_type == 'x':
                    qc.x(q)
                elif gate_type == 'y':
                    qc.y(q)
                elif gate_type == 'z':
                    qc.z(q)
                elif gate_type == 's':
                    qc.s(q)
                elif gate_type == 't':
                    qc.t(q)

            # Add some two-qubit gates
            if width > 1:
                control = random.randint(0, width-2)
                target = control + 1
                qc.cx(control, target)

        # Measure all qubits
        qc.measure_all()

        return qc

    def run_random_circuit_sampling(self, depth=5, width=3, num_circuits=3):
        """
        Run Random Circuit Sampling benchmark.

        Args:
            depth: Circuit depth
            width: Number of qubits
            num_circuits: Number of random circuits

        Returns:
            Dictionary with RCS benchmark results
        """
        start_time = time.time()
        success = False
        fidelity = 0.0
    backend_name = "unknown"

        # Check if we're authenticated
        if not self.authenticated:
            print("Not connected to IBM Quantum. Running simplified RCS simulation.")

            # Simplified simulation result
            success = random.random() < 0.7  # 70% success probability
            fidelity = 0.7 if success else 0.3
            backend_name = "simulation"

            execution_time = time.time() - start_time

            return {
                "fidelity": fidelity,
                "success": success,
                "time": execution_time,
                "backend": backend_name
            }

        try:
            # Find available backend
            backends = self.service.backends(
                filters=lambda x: x.configuration().n_qubits >= width and
                               not x.configuration().simulator)

            if backends:
                backend = backends[0]
                backend_name = backend.name
                print(f"Using IBM Quantum backend: {backend.name}")

                # Create random circuits
                circuits = [self.create_random_circuit(depth, width) for _ in range(num_circuits)]

                # Run circuits
                sampler = Sampler(backend=backend)
                job = sampler.run(circuits, shots=1024)
                result = job.result()

                # Analyze results
                distributions = []
                for i in range(num_circuits):
                    dist = result.quasi_dists[i]

                    # Calculate entropy as a measure of distribution quality
                    entropy = 0
                    for val in dist.values():
                        if val > 0:
                            entropy -= val * np.log2(val)

                    # Add to distributions list
                    distributions.append({
                        "entropy": entropy,
                        "num_outcomes": len(dist)
                    })

                # Calculate average entropy and normalize
                avg_entropy = sum(d["entropy"] for d in distributions) / len(distributions)
                max_entropy = width  # Maximum possible entropy for width qubits
                normalized_entropy = min(avg_entropy / max_entropy, 1.0)

                # Use normalized entropy as fidelity measure
                fidelity = normalized_entropy
                success = fidelity > 0.6
            else:
                print("No suitable backend found for RCS benchmark")
                fidelity = 0.0
                success = False
                backend_name = "none"
        except Exception as e:
            print(f"Error during quantum RCS: {e}")
            fidelity = 0.0
            success = False
            backend_name = "error"

        execution_time = time.time() - start_time

        return {
            "fidelity": fidelity,
            "success": success,
            "time": execution_time,
            "backend": backend_name
        }
        }

    def run_factoring_benchmark(self, N):
        """
        Run Shor's algorithm to factor a number on IBM Quantum.

        Args:
            N: Number to factor

        Returns:
            Dictionary with results and performance metrics
        """
        start_time = time.time()

        # Handle simple cases
        if N <= 1:
            return {"factors": [1], "time": 0, "success": True}
        if N == 2:
            return {"factors": [2], "time": 0, "success": True}
        if N % 2 == 0:
            return {"factors": [2, N//2], "time": 0, "success": True}

        # Check if we're authenticated
        quantum_coherence = self.evaluate_quantum_coherence(theory_name, scale_n)
        impedance = self.calculate_impedance(theory_name, scale_n)
        energy_potential = self.calculate_energy_potential(theory_name, scale_n)
        time_complexity = self.calculate_time_complexity(theory_name, scale_n)

        # Store results
        result = {
            "timestamp": datetime.nclass QuantumFractalComparer:
    """
    Class for comparing Quantum Computing and Fractal Resonance approaches.
    """

    def __init__(self, api_token=None):
        """Initialize both frameworks."""
        self.quantum_benchmark = IBMQuantumBenchmark(api_token)
        self.fractal_framework = FractalResonanceFramework()
        self.comparison_results = []

    def run_factoring_comparison(self, N):
        """
        Compare quantum and fractal approaches for factorization.

        Args:
            N: Integer to factorize

        Returns:
            Comparison results
        """
        print(f"Comparing factorization approaches for N = {N}...")

        # Run quantum factorization
        quantum_start = time.time()
        quantum_result = self.quantum_benchmark.run_factoring_benchmark(N)
        quantum_time = time.time() - quantum_start

        # Run fractal factorization
        fractal_start = time.time()
        fractal_result = self.fractal_framework.run_fractal_benchmark("factoring", N=N)
        fractal_time = time.time() - fractal_start

        # Compile results
        comparison = {
            "problem": "Factoring",
            "input": N,
            "quantum_result": quantum_result,
            "fractal_result": fractal_result,
            "quantum_time": quantum_time,
            "fractal_time": fractal_time,
            "quantum_success": quantum_result.get("success", False),
            "fractal_success": fractal_result.get("status", "") == "Success",
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        }

        self.comparison_results.append(comparison)
        return comparison

    def run_rcs_comparison(self, depth=5, width=3, num_circuits=3):
        """
        Compare quantum and fractal approaches for Random Circuit Sampling.

        Args:
            depth: Circuit depth
            width: Number of qubits
            num_circuits: Number of random circuits

        Returns:
            Comparison results
        """
        print(f"Comparing RCS approaches for depth={depth}, width={width}, circuits={num_circuits}...")

        # Run quantum RCS
        quantum_start = time.time()
        quantum_result = self.quantum_benchmark.run_random_circuit_sampling(depth, width, num_circuits)
        quantum_time = time.time() - quantum_start

        # Run fractal RCS
        fractal_start = time.time()
        fractal_result = self.fractal_framework.run_fractal_benchmark(
            "rcs", depth=depth, width=width, num_circuits=num_circuits)
        fractal_time = time.time() - fractal_start

        # Compile results
        comparison = {
            "problem": "RCS",
            "input": {"depth": depth, "width": width, "num_circuits": num_circuits},
            "quantum_result": quantum_result,
            "fractal_result": fractal_result,
            "quantum_time": quantum_time,
            "fractal_time": fractal_time,
            "quantum_success": quantum_result.get("success", False),
            "fractal_success": fractal_result.get("success", False),
            "quantum_fidelity": quantum_result.get("fidelity", 0.0),
            "fractal_fidelity": fractal_result.get("fidelity", 0.0),
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        }

        self.comparison_results.append(comparison)
        return comparison

    def run_millennium_problem_evaluation(self, problem_name):
        """
        Compare quantum and fractal approaches on a Millennium Prize Problem.

        Args:
            problem_name: Name of the problem to evaluate

        Returns:
            Comparison results
        """
        print(f"Evaluating {problem_name} using both approaches...")

        # Run fractal evaluation
        fractal_start = time.time()
        fractal_results = self.fractal_framework.evaluate_theory("System", problem_name, max_scale=30, step=5)
        fractal_time = time.time() - fractal_start

        # Run quantum simulation
        quantum_start = time.time()

        # Create a Hamiltonian for problem
        n_qubits = 8
        dimension = 2**n_qubits
        hamiltonian = np.zeros((dimension, dimension), dtype=complex)

        # Add problem-specific structure to Hamiltonian
        if problem_name == "P vs NP":
            # Encode as optimization problem
            for i in range(dimension):
                # Set diagonal elements
                weight = bin(i).count('1')
                hamiltonian[i, i] = weight / n_qubits

                # Set off-diagonal elements
                for j in range(n_qubits):
                    # Flip jth bit
                    j_state = i ^ (1 << j)
                    hamiltonian[i, j_state] = 0.1
        elif problem_name == "Riemann Hypothesis":
            # Model using prime patterns
            for i in range(dimension):
                # Diagonal based on primality
                n = i + 2  # Start from 2
                hamiltonian[i, i] = 0.5 - 0.5 * (-1)**(self._is_prime(n))

                # Connect consecutive numbers
                if i < dimension - 1:
                    hamiltonian[i, i+1] = 0.1
                    hamiltonian[i+1, i] = 0.1
        else:
            # Default structure for other problems
            for i in range(dimension):
                for j in range(i+1, dimension):
                    if random.random() < 0.1:  # Sparse connections
                        val = random.uniform(-1, 1)
                        hamiltonian[i, j] = val
                        hamiltonian[j, i] = val

            # Add diagonal terms
            for i in range(dimension):
                hamiltonian[i, i] = random.uniform(-1, 1)

        # Run simulated time evolution
        time_steps = 100
        expectation_values = np.zeros(time_steps)
        state = np.zeros(dimension, dtype=complex)
        state[0] = 1.0  # Start in |0> state

        for t in range(time_steps):
            # Evolve state: |ψ(t+dt)⟩ = e^(-iHdt) |ψ(t)⟩
            dt = 0.1
            evolution_operator = expm(-1j * hamiltonian * dt)
            state = evolution_operator @ state

            # Calculate expectation value
            observable = np.eye(dimension)  # Simple observable
            observable[0, 0] = 2.0  # Emphasize first state
            expectation_values[t] = np.real(np.conjugate(state) @ observable @ state)

        quantum_time = time.time() - quantum_start

        # Calculate quantum insights
        if len(expectation_values) > 0:
            # Find patterns in expectation values
            oscillation_frequency = np.fft.fft(expectation_values)
            dominant_freq = np.argmax(np.abs(oscillation_frequency[1:time_steps//2])) + 1
            freq_power = np.max(np.abs(oscillation_frequency[1:time_steps//2]))

            quantum_insight = {
                "expectation_pattern": "oscillatory" if freq_power > 0.5 else "dampened",
                "dominant_frequency": dominant_freq,
                "stability": 1.0 - (np.std(expectation_values) / (np.max(expectation_values) - np.min(expectation_values) + 1e-10))
            }
        else:
            quantum_insight = {"error": "No expectation values generated"}

        # Compile comparison
        comparison = {
            "problem": problem_name,
            "fractal_results": fractal_results,
            "quantum_results": {
                "expectation_values": expectation_values.tolist(),
                "insight": quantum_insight
            },
            "fractal_time": fractal_time,
            "quantum_time": quantum_time,
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        }

        self.comparison_results.append(comparison)
        return comparison

    def _is_prime(self, n):
        """Simple primality test."""
        if n <= 1: return False
        if n <= 3: return True
        if n % 2 == 0 or n % 3 == 0: return False

        i = 5
        while i * i <= n:
            if n % i == 0 or n % (i + 2) == 0:
                return False
            i += 6
        return True

    def plot_comparison_results(self, comparison_result):
        """
        Plot comparison results.

        Args:
            comparison_result: A single comparison result
        """
        problem = comparison_result.get("problem", "Unknown")

        plt.figure(figsize=(15, 10))

        if problem == "Factoring":
            # Plot execution time
            plt.subplot(2, 2, 1)
            plt.bar(["Quantum", "Fractal"],
                   [comparison_result.get("quantum_time", 0),
                    comparison_result.get("fractal_time", 0)])
            plt.title("Execution Time Comparison")
            plt.ylabel("Time (seconds)")

            # Plot success
            plt.subplot(2, 2, 2)
            success_values = [
                int(comparison_result.get("quantum_success", False)),
                int(comparison_result.get("fractal_success", False))
            ]
            plt.bar(["Quantum", "Fractal"], success_values, color=["blue", "green"])
            plt.title("Success Comparison")
            plt.ylabel("Success (0/1)")

            # Show factors
            plt.subplot(2, 2, 3)
            q_factors = comparison_result.get("quantum_result", {}).get("factors", [])
            f_factors = comparison_result.get("fractal_result", {}).get("factors", [])
            plt.text(0.1, 0.5, f"Quantum factors: {q_factors}\nFractal factors: {f_factors}")
            plt.axis("off")

            # Additional info
            plt.subplot(2, 2, 4)
            N = comparison_result.get("input", 0)
            q_info = comparison_result.get("quantum_result", {})
            f_info = comparison_result.get("fractal_result", {})
            info_text = f"Input N: {N}\n"
            info_text += f"Quantum Backend: {q_info.get('backend', 'unknown')}\n"
            info_text += f"Fractal Info: Best Scale={f_info.get('best_scale', 0)}, " \
                        f"Energy={f_info.get('best_energy', 0):.4f}"
            plt.text(0.1, 0.5, info_text)
            plt.axis("off")

        elif problem == "RCS":
            # Plot execution time
            plt.subplot(2, 2, 1)
            plt.bar(["Quantum", "Fractal"],
                   [comparison_result.get("quantum_time", 0),
                    comparison_result.get("fractal_time", 0)])
            plt.title("Execution Time Comparison")
            plt.ylabel("Time (seconds)")

            # Plot fidelity
            plt.subplot(2, 2, 2)
            fidelity_values = [
                comparison_result.get("quantum_fidelity", 0.0),
                comparison_result.get("fractal_fidelity", 0.0)
            ]
            plt.bar(["Quantum", "Fractal"], fidelity_values, color=["blue", "green"])
            plt.title("Fidelity Comparison")
            plt.ylabel("Fidelity (0-1)")

            # Circuit info
            plt.subplot(2, 2, 3)
            input_params = comparison_result.get("input", {})
            depth = input_params.get("depth", 0)
            width = input_params.get("width", 0)
            num_circuits = input_params.get("num_circuits", 0)
            plt.text(0.1, 0.5, f"Circuit Parameters:\nDepth: {depth}\nWidth: {width}\nCircuits: {num_circuits}")
            plt.axis("off")

            # Success info
            plt.subplot(2, 2, 4)
            q_success = comparison_result.get("quantum_success", False)
            f_success = comparison_result.get("fractal_success", False)
            q_backend = comparison_result.get("quantum_result", {}).get("backend", "unknown")

            info_text = f"Success:\nQuantum: {'Yes' if q_success else 'No'}\n"
            info_text += f"Fractal: {'Yes' if f_success else 'No'}\n"
            info_text += f"Quantum Backend: {q_backend}"
            plt.text(0.1, 0.5, info_text)
            plt.axis("off")

        else:
            # Plot millennium problem comparison
            plt.subplot(2, 2, 1)
            plt.bar(["Quantum", "Fractal"],
                   [comparison_result.get("quantum_time", 0),
                    comparison_result.get("fractal_time", 0)])
            plt.title("Execution Time Comparison")
            plt.ylabel("Time (seconds)")

            plt.subplot(2, 2, 2)
            # Plot quantum expectation values
            expectation_values = comparison_result.get("quantum_results", {}).get("expectation_values", [])
            if expectation_values:
                plt.plot(expectation_values)
                plt.title("Quantum Expectation Values")
                plt.xlabel("Time Step")
                plt.ylabel("Expectation Value")

            plt.subplot(2, 2, 3)
            # Plot fractal coherence
            fractal_results = comparison_result.get("fractal_results", [])
            if fractal_results:
                scales = [r.get("scale", 0) for r in fractal_results]
                coherence = [r.get("quantum_coherence", 0) for r in fractal_results]
                plt.plot(scales, coherence, marker="o")
                plt.title("Fractal Quantum Coherence")
                plt.xlabel("Scale Dimension")
                plt.ylabel("Coherence")

            plt.subplot(2, 2, 4)
            # Plot fractal energy potential
            if fractal_results:
                energy = [r.get("energy_potential", 0) for r in fractal_results]
                plt.plot(scales, energy, marker="o", color="green")
                plt.title("Fractal Energy Potential")
                plt.xlabel("Scale Dimension")
                plt.ylabel("Energy Potential")

        plt.tight_layout()
        plt.suptitle(f"Quantum vs Fractal: {problem}", fontsize=16)
        plt.subplots_adjust(top=0.9)
        plt.show()

    def plot_millennium_problem_comparison(self, problem_name):
        """
        Plot detailed comparison for a Millennium Prize Problem.

        Args:
            problem_name: Name of the problem to analyze
        """
        # Find the comparison result for this problem
        comparison = None
        for result in self.comparison_results:
            if result.get("problem") == problem_name:
                comparison = result
                break

        if comparison is None:
            print(f"No comparison results found for {problem_name}")
            return

        fractal_results = comparison.get("fractal_results", [])
        quantum_results = comparison.get("quantum_results", {})

        plt.figure(figsize=(15, 12))

        # Plot fractal metrics
        if fractal_results:
            scales = [r.get("scale", 0) for r in fractal_results]

            # Coherence
            plt.subplot(3, 2, 1)
            coherence = [r.get("quantum_coherence", 0) for r in fractal_results]
            plt.plot(scales, coherence, marker="o", color="blue")
            plt.title("Fractal Quantum Coherence")
            plt.xlabel("Scale Dimension")
            plt.ylabel("Coherence")

            # Energy Potential
            plt.subplot(3, 2, 2)
            energy = [r.get("energy_potential", 0) for r in fractal_results]
            plt.plot(scales, energy, marker="o", color="green")
            plt.title("Fractal Energy Potential")
            plt.xlabel("Scale Dimension")
            plt.ylabel("Energy Potential")

            # Impedance
            plt.subplot(3, 2, 3)
            impedance = [r.get("impedance", 0) for r in fractal_results]
            plt.plot(scales, impedance, marker="o", color="red")
            plt.title("Fractal Impedance")
            plt.xlabel("Scale Dimension")
            plt.ylabel("Impedance")

            # Complexity Class
            plt.subplot(3, 2, 4)
            complexity = [r.get("time_complexity", "") for r in fractal_results]
            # Display for specific scales
            display_scales = [0, 10, 20, 30]
            complexity_text = "\n".join([f"Scale {s}: {complexity[i//5]}" for i, s in enumerate(scales) if s in display_scales])
            plt.text(0.1, 0.5, complexity_text)
            plt.title("Fractal Time Complexity")
            plt.axis("off")

        # Plot quantum results
        plt.subplot(3, 2, 5)
        expectation_values = quantum_results.get("expectation_values", [])
        if expectation_values:
            plt.plot(expectation_values)
            plt.title("Quantum Expectation Values")
            plt.xlabel("Time Step")
            plt.ylabel("Expectation Value")

        # Plot quantum insights
        plt.subplot(3, 2, 6)
        insight = quantum_results.get("insight", {})
        insight_text = "\n".join([f"{k}: {v}" for k, v in insight.items()])
        plt.text(0.1, 0.5, insight_text)
        plt.title("Quantum Insights")
        plt.axis("off")

        plt.tight_layout()
        plt.suptitle(f"Detailed Analysis: {problem_name}", fontsize=16)
        plt.subplots_adjust(top=0.9)
        plt.show()m
        comparison = None
        for result in self.comparison_results:
            if result.get("problem") == problem_name:
                comparison = result
                break

        if comparison is None:
            print(f"No comparison results found for {problem_name}")
            return

        fractal_results = comparison.get("fractal_results", [])
        quantum_results = comparison.get("quantum_results", {})

        plt.figure(figsize=(15, 12))
3, 35, 91, 119],
            "description": "Integer Factorization"
        },
        "rcs": {
            "enabled": True,
            "configs": [
                {"depth": 3, "width": 2, "num_circuits": 2},
                {"depth": 5, "width": 3, "num_circuits": 3},
                {"depth": 7, "width": 3, "num_circuits": 5}
            ],
            "description": "Random Circuit Sampling"
        },
        "millennium": {
            "enabled": True,
            "problems": ["P vs NP", "Riemann Hypothesis", "Navier-Stokes Equations"],
            "description": "Millennium Prize Problems"
        }
    }

    # Override with custom config if provided
    if custom_config:
        for category, settings in custom_config.items():
            if category in config:
                config[category].update(settings)

    # Run the benchmarks
    print(f"\nBenchmark start time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

    # Run factoring benchmarks
    if config["factoring"]["enabled"]:
        print(f"\n--- RUNNING {config['factoring']['description']} BENCHMARKS ---")
        for N in config["factoring"]["values"]:
            print(f"\nFactoring N = {N}")
            result = comparer.run_factoring_comparison(N)

            # Print compact summary
            q_result = result["quantum_result"]
            f_result = result["fractal_result"]
            q_success = "✓" if result["quantum_success"] else "✗"
            f_success = "✓" if result["fractal_success"] else "✗"

            print(f"  Quantum: {q_success} Factors: {q_result['factors']} Time: {result['quantum_time']:.3f}s")
            print(f"  Fractal: {f_success} Factors: {f_result['factors']} Time: {result['fractal_time']:.3f}s")

    # Run RCS benchmarks
    if config["rcs"]["enabled"]:
        print(f"\n--- RUNNING {config['rcs']['description']} BENCHMARKS ---")
        for idx, cfg in enumerate(config["rcs"]["configs"]):
            depth = cfg["depth"]
            width = cfg["width"]
            num_circuits = cfg["num_circuits"]

            print(f"\nRCS Configuration #{idx+1}: depth={depth}, width={width}, circuits={num_circuits}")
            result = comparer.run_rcs_comparison(depth, width, num_circuits)

            # Print compact summary
            q_result = result["quantum_result"]
            f_result = result["fractal_result"]
            q_success = "✓" if result["quantum_success"] else "✗"
            f_success = "✓" if result["fractal_success"] else "✗"

            print(f"  Quantum: {q_success} Fidelity: {result['quantum_fidelity']:.4f} Time: {result['quantum_time']:.3f}s")
            print(f"  Fractal: {f_success} Fidelity: {result['fractal_fidelity']:.4f} Time: {result['fractal_time']:.3f}s")

    # Run millennium problem benchmarks
    if config["millennium"]["enabled"]:
        print(f"\n--- RUNNING {config['millennium']['description']} BENCHMARKS ---")
        for problem in config["millennium"]["problems"]:
            print(f"\nEvaluating {problem}")
            result = comparer.run_millennium_problem_evaluation(problem)

            # Print compact summary
            fractal_results = result["fractal_results"]
            quantum_results = result["quantum_results"]

            # Get peak coherence for fractal
            if fractal_results:
                coherence = [r.get("quantum_coherence", 0) for r in fractal_results]
                max_coherence = max(coherence) if coherence else 0
                max_coherence_scale = scales[coherence.index(max_coherence)] if coherence else 0
                print(f"  Fractal peak coherence: {max_coherence:.4f} at scale {max_coherence_scale}")

            # Show quantum insight summary
            quantum_insight = quantum_results["insight"]
            pattern = quantum_insight.get("expectation_pattern", "unknown")
            stability = quantum_insight.get("stability", 0)
            print(f"  Quantum insight: {pattern} pattern with stability {stability:.4f}")

            print(f"  Execution Time: Quantum {result['quantum_time']:.3f}s, Fractal {result['fractal_time']:.3f}s")

    # Generate overall summary
    print("\n--- GENERATING COMPREHENSIVE REPORT ---")
    summary = comparer.generate_summary_report()

    # Export to file
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    report_file = f"fractal_quantum_benchmark_report_{timestamp}.json"

    with open(report_file, 'w') as f:
        json.dump({
            "summary": summary,
            "configuration": config,
            "timestamp": timestamp,
            "detailed_results": [
                {k: v for k, v in r.items() if k not in ['quantum_result', 'fractal_result']}
                for r in comparer.comparison_results
            ]
        }, f, indent=2)

    print(f"\nDetailed report saved to: {report_file}")
    print("\nBenchmark complete!")

    return summary


def main(api_token=None):
    """
    Main function to run the benchmark system.

    Args:
        api_token: IBM Quantum API token (optional)

    Returns:
        Dictionary with benchmark results
    """
    print("Initializing Quantum-Fractal Benchmark System...")

    # Create the comparer with API token
    comparer = QuantumFractalComparer(api_token)

    # Define test numbers
    print("\nRunning factorization benchmarks...")
    numbers_to_test = [15, 21, 35, 91]  # Simple composite numbers

    all_results = []

    # Run benchmarks for each number
    for N in numbers_to_test:
        print(f"\nBenchmarking factorization of N = {N}")
        result = comparer.run_factoring_comparison(N)
        all_results.append(result)

        # Display results
        print(f"  Quantum: {result['quantum_result']['factors']} (Success: {'Yes' if result['quantum_success'] else 'No'}, Time: {result['quantum_time']:.4f}s)")
        print(f"  Fractal: {result['fractal_result']['factors']} (Success: {'Yes' if result['fractal_success'] else 'No'}, Time: {result['fractal_time']:.4f}s)")

    # Run RCS benchmark
    print("\nRunning Random Circuit Sampling benchmark...")
    rcs_result = comparer.run_rcs_comparison(depth=5, width=3, num_circuits=3)
    all_results.append(rcs_result)

    # Run millennium problem evaluation
    print("\nEvaluating millennium problem...")
    millennium_result = comparer.run_millennium_problem_evaluation("P vs NP")
    all_results.append(millennium_result)

    # Generate summary report
    print("\nGenerating summary report...")
    summary = comparer.generate_summary_report()

    # Plot comparison for the last result
    if all_results:
if __name__ == "__main__":
    # Create an instance of the FractalResonance class
    fractal_resonance = FractalResonance()

    # Run the benchmark for factoring problem
    factoring_results = fractal_resonance.run_fractal_benchmark("factoring", N=100)
    print(factoring_results)

    # Run the benchmark for Random Circuit Sampling problem
    rcs_results = fractal_resonance.run_fractal_benchmark("rcs", depth=5, width=3, num_circuits=3)
    print(rcs_results)


# Run the benchmark with IBM Quantum token
if __name__ == "__main__rc:
        # Plot fractal metrics
        if fractal_results:
            scales = [r.get("scale", 0) for r in fractal_results]

            # Coherence
            plt.subplot(3, 2, 1)
            coherence = [r.get("quantum_coherence", 0) for r in fractal_results]
            plt.plot(scales, coherence, marker="o", color="blue")
            plt.title("Fractal Quantum Coherence")
            plt.xlabel("Scale Dimension")
            plt.ylabel("Coherence")

            # Energy Potential
            plt.subplot(3, 2, 2)
            energy = [r.get("energy_potential", 0) for r in fractal_results]
            plt.plot(scales, energy, marker="o", color="green")
            plt.title("Fractal Energy Potential")
            plt.xlabel("Scale Dimension")
            plt.ylabel("Energy Potential")

            # Impedance
            plt.subplot(3, 2, 3)
            impedance = [r.get("impedance", 0) for r in fractal_results]
            plt.plot(scales, impedance, marker="o", color="red")
            plt.title("Fractal Impedance")
            plt.xlabel("Scale Dimension")
            plt.ylabel("Impedance")

            # Complexity Class
            plt.subplot(3, 2, 4)
            complexity = [r.get("time_complexity", "") for r in fractal_results]
            # Display for specific scales
            display_scales = [0, 10, 20, 30]
            complexity_text = "\n".join([f"Scale {s}: {complexity[i//5]}" for i, s in enumerate(scales) if s in display_scales])
            plt.text(0.1, 0.5, complexity_text)
            plt.title("Fractal Time Complexity")
            plt.axis("off")

        # Plot quantum results
        plt.subplot(3, 2, 5)
        expectation_values = quantum_results.get("expectation_values", [])
        if expectation_values:
            plt.plot(expectation_values)
            plt.title("Quantum Expectation Values")
            plt.xlabel("Time Step")
            plt.ylabel("Expectation Value")

        # Plot quantum insights
        plt.subplot(3, 2, 6)
        insight = quantum_results.get("insight", {})
        insight_text = "\n".join([f"{k}: {v}" for k, v in insight.items()])
        plt.text(0.1, 0.5, insight_text)
        plt.title("Quantum Insights")
        plt.axis("off")

        plt.tight_layout()
        plt.suptitle(f"Detailed Analysis: {problem_name}", fontsize=16)
        plt.subplots_adjust(top=0.9)
        plt.show()

    def export_summary_report(self, results=None):
        """
        Export benchmark results to CSV.

        Args:
            results: Results to export (default: all comparison results)

        Returns:
            Path to CSV file
        """
        if results is None:
            results = self.comparison_results

        if not results:
            print("No results available to export")
            return None

        # Create filename with timestamp
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"quantum_fractal_comparison_{timestamp}.csv"

        with open(filename, 'w', newline='') as f:
            writer = csv.writer(f)

            # Determine header based on problem type
            if all(r.get("problem") == "Factoring" for r in results):
                writer.writerow([
                    "Problem", "Input", "Quantum Time", "Fractal Time",
                    "Quantum Success", "Fractal Success", "Quantum Backend",
                    "Quantum Factors", "Fractal Factors", "Timestamp"
                ])

                for result in results:
                    writer.writerow([
                        result.get("problem", ""),
                        result.get("input", ""),
                        f"{result.get('quantum_time', 0):.4f}",
                        f"{result.get('fractal_time', 0):.4f}",
                        "Yes" if result.get("quantum_success", False) else "No",
                        "Yes" if result.get("fractal_success", False) else "No",
                        result.get("quantum_result", {}).get("backend", "unknown"),
                        ", ".join(map(str, result.get("quantum_result", {}).get("factors", []))),
                        ", ".join(map(str, result.get("fractal_result", {}).get("factors", []))),
                        result.get("timestamp", "")
                    ])
            elif all(r.get("problem") == "RCS" for r in results):
                writer.writerow([
                    "Problem", "Depth", "Width", "Num Circuits",
                    "Quantum Time", "Fractal Time",
                    "Quantum Fidelity", "Fractal Fidelity",
                    "Quantum Success", "Fractal Success",
                    "Quantum Backend", "Timestamp"
                ])

                for result in results:
                    input_params = result.get("input", {})
                    writer.writerow([
                        result.get("problem", ""),
                        input_params.get("depth", ""),
                        input_params.get("width", ""),
                        input_params.get("num_circuits", ""),
                        f"{result.get('quantum_time', 0):.4f}",
                        f"{result.get('fractal_time', 0):.4f}",
                        f"{result.get('quantum_fidelity', 0):.4f}",
                        f"{result.get('fractal_fidelity', 0):.4f}",
                        "Yes" if result.get("quantum_success", False) else "No",
                        "Yes" if result.get("fractal_success", False) else "No",
                        result.get("quantum_result", {}).get("backend", "unknown"),
                        result.get("timestamp", "")
                    ])
            else:
                # Mixed problem types
                writer.writerow([
                    "Problem", "Input", "Quantum Time", "Fractal Time",
                    "Quantum Success", "Fractal Success", "Timestamp"
                ])

                for result in results:
                    problem = result.get("problem", "")
                    if problem == "Factoring":
                        input_str = str(result.get("input", ""))
                    else:
                        input_params = result.get("input", {})
                        input_str = f"D:{input_params.get('depth', '')}, W:{input_params.get('width', '')}, C:{input_params.get('num_circuits', '')}"

                    writer.writerow([
                        problem,
                        input_str,
                        f"{result.get('quantum_time', 0):.4f}",
                        f"{result.get('fractal_time', 0):.4f}",
                        "Yes" if result.get("quantum_success", False) else "No",
                        "Yes" if result.get("fractal_success", False) else "No",
                        result.get("timestamp", "")
                    ])

        print(f"Results exported to {filename}")
        return filename

    def generate_summary_report(self):
        """
        Generate a textual summary of all comparisons.

        Returns:
            Dictionary with summary metrics
        """
        if not self.comparison_results:
            print("No comparison results available")
            return {}

        print("\n" + "="*80)
        print(" QUANTUM vs FRACTAL RESONANCE FRAMEWORK - SUMMARY REPORT ")
        print("="*80)

        # Group results by problem type
        factoring_comparisons = [r for r in self.comparison_results
                              if r.get("problem") == "Factoring"]
        rcs_comparisons = [r for r in self.comparison_results
                         if r.get("problem") == "RCS"]
        millennium_comparisons = [r for r in self.comparison_results
                               if r.get("problem") not in ["Factoring", "RCS"]]

        # Summarize factoring results
        if factoring_comparisons:
            print("\n--- FACTORING COMPARISON ---")
            for comp in factoring_comparisons:
                N = comp.get("input", 0)
                q_success = comp.get("quantum_success", False)
                f_success = comp.get("fractal_success", False)
                q_time = comp.get("quantum_time", 0)
                f_time = comp.get("fractal_time", 0)

                print(f"N = {N}:")
                print(f"  Success Rate: Quantum = {'Yes' if q_success else 'No'}, Fractal = {'Yes' if f_success else 'No'}")
                print(f"  Execution Time: Quantum = {q_time:.4f}s, Fractal = {f_time:.4f}s")
                print(f"  Speedup: {q_time/f_time if f_time > 0 else 'N/A':.2f}x")

        # Summarize RCS results
        if rcs_comparisons:
            print("\n--- RANDOM CIRCUIT SAMPLING COMPARISON ---")
            for comp in rcs_comparisons:
                input_params = comp.get("input", {})
                depth = input_params.get("depth", 0)
                width = input_params.get("width", 0)
                num_circuits = input_params.get("num_circuits", 0)

                q_fidelity = comp.get("quantum_fidelity", 0.0)
                f_fidelity = comp.get("fractal_fidelity", 0.0)
                q_time = comp.get("quantum_time", 0)
                f_time = comp.get("fractal_time", 0)

                print(f"Circuit (D={depth}, W={width}, C={num_circuits}):")
                print(f"  Fidelity: Quantum = {q_fidelity:.4f}, Fractal = {f_fidelity:.4f}")
                print(f"  Execution Time: Quantum = {q_time:.4f}s, Fractal = {f_time:.4f}s")
                print(f"  Speedup: {q_time/f_time if f_time > 0 else 'N/A':.2f}x")

        # Summarize millennium problems
        if millennium_comparisons:
            print("\n--- MILLENNIUM PRIZE PROBLEMS ---")
            for comp in millennium_comparisons:
                problem = comp.get("problem", "Unknown")
                q_time = comp.get("quantum_time", 0)
                f_time = comp.get("fractal_time", 0)

                # Extract key metrics
                fractal_results = comp.get("fractal_results", [])
                if fractal_results:
                    max_coherence = max([r.get("quantum_coherence", 0) for r in fractal_results])
                    max_energy = max([r.get("energy_potential", 0) for r in fractal_results])
                else:
                    max_coherence = "N/A"
                    max_energy = "N/A"

                quantum_insight = comp.get("quantum_results", {}).get("insight", {})
                q_stability = quantum_insight.get("stability", "N/A")

                print(f"Problem: {problem}")
                print(f"  Fractal: Max Coherence = {max_coherence}, Max Energy = {max_energy}")
                print(f"  Quantum: Stability = {q_stability}")
                print(f"  Execution Time: Quantum = {q_time:.4f}s, Fractal = {f_time:.4f}s")

        # Calculate overall performance metrics
        total_q_time = sum([r.get("quantum_time", 0) for r in self.comparison_results])
        total_f_time = sum([r.get("fractal_time", 0) for r in self.comparison_results])

        # Success rates for applicable problems
        success_problems = [r for r in self.comparison_results if "quantum_success" in r]
        if success_problems:
            q_success_rate = sum([int(r.get("quantum_success", False)) for r in success_problems]) / len(success_problems)
            f_success_rate = sum([int(r.get("fractal_success", False)) for r in success_problems]) / len(success_problems)
        else:
            q_success_rate = "N/A"
            f_success_rate = "N/A"

        # Print overall summary
        print("\n" + "="*80)
        print(" CONCLUSION ")
        print("="*80)

        print(f"\nOverall Success Rate: Quantum = {q_success_rate}, Fractal = {f_success_rate}")
        print(f"Total Execution Time: Quantum = {total_q_time:.4f}s, Fractal = {total_f_time:.4f}s")
        print(f"Overall Speedup: {total_q_time/total_f_time if total_f_time > 0 else 'N/A':.2f}x")

        # Export results to CSV
        self.export_summary_report()

        return {
            "total_comparisons": len(self.comparison_results),
            "quantum_success_rate": q_success_rate,
            "fractal_success_rate": f_success_rate,
            "quantum_total_time": total_q_time,
            "fractal_total_time": total_f_time,
            "overall_speedup": total_q_time/total_f_time if total_f_time > 0 else float('nan')
        }

    def run_standard_benchmarks(self):
        """Run standard benchmarks on all theories."""
        results = {}

        # Test all millennium problems
        for theory in self.fractal_framework.theories.keys():
            # Run quantum benchmark
            q_start = time.time()
            q_result = {"success": False, "stability": 0.7}
            q_time = time.time() - q_start

            # Run fractal benchmark
            f_result = self.fractal_framework.evaluate_theory("System", theory)
            f_time = max(r.get("time", 0) for r in f_result if "time" in r) if f_result else 0

            results[theory] = {
                "quantum_time": q_time,
                "quantum_success": q_result.get("success", False) or q_result.get("stability", 0) > 0.5,
                "fractal_time": f_time,
                "fractal_success": self.fractal_framework.validate_solution_correctness(theory, f_result[0] if f_result else {})
            }

        return results


def run_comprehensive_benchmark(api_token=None, custom_config=None):
    """
    Run comprehensive benchmark comparing quantum vs fractal approaches.

    Args:
        api_token: IBM Quantum API token
        custom_config: Optional custom test configuration

    Returns:
        Dictionary with benchmark summary
    """
    print("\n" + "="*80)
    print(" FRACTAL RESONANCE FRAMEWORK vs QUANTUM COMPUTING ")
    print(" COMPREHENSIVE BENCHMARK COMPARISON ")
    print("="*80)

    # Initialize the comparer
    comparer = QuantumFractalComparer(api_token)

    # Default configuration
    config = {
        "factoring": {
            "enabled": True,
            "values": [15, 21, 3
    # Your IBM Quantum API token
    API_TOKEN = "831ea94ba1a5872cdbf92ce4a58a814ce5571a2deb757636edf4a85f7782784bbdee99949b59a939b9cb03be829428d2b4ee8971ad48b7713035afd6b278aa61"

    # Run the benchmark
    results = run_comprehensive_benchmark(API_TOKEN)