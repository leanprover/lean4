Automatic Builds at [Travis](https://travis-ci.org/)
----------------------------------------------------

When a commit is submitted to the the main repository,
a service hook at github will automatically build Lean using
[Travis](https://travis-ci.org/).

There is a way to prevent a push from being built.
Pushes that have either ```[ci skip]``` or ```[skip ci]``` *anywhere* in one of the
commit messages will be ignored. 

Automatic builds can be enabled for any *fork* of the Lean repository.
We just have to go to our fork page at github; select `settings` (it is an icon on the right hand side of the page);
select `Service Hooks`; select `Travis`; and provide the required information.
We must have an account at Travis.

By default, build reports are sent to the [lean-build](https://groups.google.com/forum/#!forum/lean-build) Google group.
You can change that by modifying the file [.travis.yml](../../.travis.yml) in the Lean root directory. The file contains a
`recipients:` entry.
