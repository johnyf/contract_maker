About
=====

Construction of temporal logic contracts for distributed systems,
starting from GR(1) specifications.
This implementation is experimental, so expect changes.


Installation
============

The dependencies are listed in the file `requirements.txt`. Installing a
suitable version of the package `dd` can be done as follows.

```shell
pip uninstall --yes dd
pip install cython
pip download --no-dependencies dd==0.5.1
tar xzf dd-*.tar.gz
cd dd-*/
export CUDD_VERSION=3.0.0
export CUDD_GZ=cudd-${CUDD_VERSION}.tar.gz
curl -sSL https://sourceforge.net/projects/cudd-mirror/files/${CUDD_GZ}/download > ${CUDD_GZ}
tar -xzf ${CUDD_GZ}
python -c 'from download import make_cudd; make_cudd()'
python setup.py install --cudd
```

These steps will download and build the C library CUDD, and then build and
install `dd`, including the Cython module `dd.cudd`. The steps are based on
[this `.travis.yml`](https://github.com/tulip-control/tulip-control/blob/ce54897c242689f45ad33650f157bf1805b35ed6/.travis.yml#L45-L56).
The repository `contract_maker` requires `dd==0.5.1` (as listed in the file
`requirements.txt`), and the above steps correspond to that version of `dd`.


References
==========

Filippidis I., Murray R.M.<br>
  [Symbolic construction of GR(1) contracts for systems with full information][1]<br>
  The 2016 American Control Conference (ACC)<br>
  Boston, MA, July 6--8, 2016


Filippidis I., Murray R.M.<br>
  [Symbolic construction of GR(1) contracts for synchronous systems with full information][2]<br>
  ArXiv CoRR abs/1508.02705, August, 2015
  (technical report with proofs and more details)


License
=======
[BSD-3](http://opensource.org/licenses/BSD-3-Clause), see file `LICENSE`.

[1]: http://resolver.caltech.edu/CaltechCDSTR:2016.003
[2]: https://arxiv.org/abs/1508.02705
