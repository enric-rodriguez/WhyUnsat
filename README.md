# WhyUnsat

A timeless anytime efficient tool for giving a (minimal) explanation of unsatisfiability of a SAT instance in terms of its original high-level constraints, aimed at planning, timetabling and scheduling applications.

## Getting Started

### Dependencies

WhyUnsat requires:

* ``g++``.
* ``mpic++``. You can install it using the command:

```
   sudo apt install openmpi-bin libopenmpi-dev
```

WhyUnsat also requires a SAT solver and a proof trimmer. The available version is prepared for using ``kissat`` and ``dpr-trim``, respectively.

* [``kissat``](https://github.com/arminbiere/kissat/)
* [``dpr-trim``](https://github.com/marijnheule/dpr-trim/)


### Compiling and Installing

* Set the paths where the SAT solver and the proof trimmer are installed in the source file ``WhyUnsat.cpp`` at the lines starting with `SET THE SAT SOLVER AND PROOF TRIMMER`.
* Type ``make``


### Executing

* To run the program on a multi-core single computer, e.g. with 8 processes on the formula in ``infile.gcnf``, constraint explanation file ``constraintMessages.txt`` and proof file ``CPproof.proof``, with a strategy of trimming until improvement is less than 2%:

    ```
       mpirun -np 8   WhyUnsat infile.gcnf  -exp constraintMessages.txt -percent 2  -proof CPproof.proof
    ```

* To run the program on a SLURM cluster, upload and adapt the script ``runWhyUnsat.slurm`` (queue, output filename, error filename, timelimit, etc.), compile as usual with ``make`` and submit the job by typing:

    ```
       sbatch runWhyUnsat.slurm
    ```

* See ``WhyUnsat -help`` for more options.


## Examples

Three different application problems are provided as examples:

* ``benchmarksRCPSP``
* ``benchmarksEvents``
* ``benchmarksTimetabling``

Each of these directories contains a brief description of the problem (file ``description.txt``) and 20 unsatisfiable instances (files ``problem*.pl``) together with the corresponding files ``infile*.gcnf``, ``constraintMessages*.txt`` and ``CPproof*.proof`` for running ``WhyUnsat``.


## Authors

Robert Nieuwenhuis (roberto@cs.upc.edu)

Albert Oliveras (oliveras@cs.upc.edu)

Enric Rodríguez-Carbonell (erodri@cs.upc.edu)
