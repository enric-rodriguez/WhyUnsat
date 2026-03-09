#!/bin/bash
#SBATCH --job-name=WhyUnsat
#SBATCH --nodes=8
#SBATCH --ntasks-per-node=2
#SBATCH --time=00:30:00
#SBATCH -p solver # short, solver, etc....
#SBATCH --account=solver
#SBATCH --output=WhyUnsat.out
#SBATCH --error=WhyUnsat.err

mpirun -np $SLURM_NTASKS ./WhyUnsat infile.gcnf  -exp constraintMessages.txt -percent 2 -proof CPproof.proof

exit
