# sat_solver_examples
examples of using a SAT/SMT solver

Run monosat grid router (i.e. PCB net, fluidic pipe, roads) with:
```
# edit grid_router.py to change the "test_example" variable
# test_example = 1    ---   inputs and outputs are left-to-right, or up-to-down
# test_example = 2    ---   WIP
# test_example = 3    ---   Use PCRT format, input filepath as command-line argument
# default is currently PCRT input

cd monosat
python3 grid_router.py simple90.pcrt
cat sol_out
```

Note that simple90.pcrt was taken from Sam Bayless's monosat routing examples.
