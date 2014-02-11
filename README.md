# Verification of CRDTs with Isabelle

The theory files can be checked with [Isabelle 2013-2](http://isabelle.in.tum.de/).
Isabelle 2013-1 and other older verisions are not compatible.

## Code structure:

* `all.thy`: theory which imports all other theory-files (
	can be used to find unused theorems in all files and to load everything at once)
* `src/framework/`: Contains the general framework which applies to all CRDTs
* `src/crdts/`: Contains the different verified CRDTs. For each CRDT there are several files with the following postfixes:
	* `[crdt-name]_spec`: the specification of the data type
	* `[crdt-name]_[implementation-name]`: an implementation of the data type
	* `[crdt-name]_[implementation-name]_convergence`: convergence proofs for the implementation
	* `[crdt-name]_[implementation-name]_valid`: proofs that the implementation is conform to its specification
