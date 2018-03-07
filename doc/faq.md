Frequently Asked Questions
==========================

* What is Lean?

Lean is a new open source theorem prover being developed at Microsoft Research.
It is a research project that aims to bridge the gap between interactive and automated theorem proving.
Lean can be also used as a programming language. Actually, some Lean features are implemented in Lean itself.

* Are pull requests welcome?

In the past, we accepted most pull requests. This practice produced hard to maintain code, performance problems, and bugs.
It takes time to review a pull request and make sure it is correct, useful and is not in conflict with our plans.
Small bug fixes (few lines of code) are always welcome. Any other kind of unrequested pull request is not.
Thus, before implementing a feature or modifying the system, please ask whether the change is welcome or not.

* Should I use Lean?

Lean is under heavy development, and we are constantly trying new
ideas and tweaking the system.  It is a research project and not a product.
Things change rapidly, and we constantly break backward compatibility.
Lean comes "as is", you should not expect we will fix bugs and/or add new features for your project.
We have our own priorities, and will not change them to accommodate your needs.
Even if you implement a new feature or fix a bug, we may not want to merge it because
it may conflict with our plans for Lean, it may not be performant, we may not want to maintain it,
we may be busy, etc. If you really need this new feature or bug fix, we suggest you create your own fork and maintain it yourself.

* Where is the documentation?

The [Lean tutorial](https://leanprover.github.io/theorem_proving_in_lean) is a good introduction to the system.
It may contain a few inconsistencies due to recent changes, but we try to keep it in sync.
The reference manual is work in progress, and we don't know when it will be ready.
The core and math libraries contain many definitions and proofs, they demonstrate how we expect the system to be used.
If the lack of documentation is an issue, then Lean is not a good match for you.
Documentation is not the main priority right now. Recall that Lean is a research project and not a product.
A public and very active chat room dedicated to Lean is open on [Zulip](https://leanprover.zulipchat.com).
It is a good place to interact with other Lean users.
You may also join the [Lean user forum](https://groups.google.com/forum/#!forum/lean-user) on Google Groups.

* Should I use Lean to teach a course?

Lean has been used to teach courses on logic, type theory and programming languages at CMU and the University of Washington.
The lecture notes for the CMU course [Logic and Proof](https://leanprover.github.io/logic_and_proof) are available online.
If you decide to teach a course using Lean, we suggest you prepare all material before the beginning of the course, and
make sure that Lean attends all your needs. You should not expect we will fix bugs and/or add features needed for your course.

* Are there IDEs for Lean?

Yes, the two main ones are for [Emacs](https://github.com/leanprover/lean-mode) and [VS Code](https://github.com/leanprover/vscode-lean).
The Emacs Lean mode is available via [MELPA](https://melpa.org/). The VS Code Lean extension is available on its marketplace.

* Is Lean sound? How big is the kernel? Should I trust it?

Lean has a relatively small kernel. The [leanchecker](https://github.com/leanprover/lean/tree/master/src/checker) is a bare-bones version of the Lean kernel.
There are also two independent checkers: [tc](https://github.com/leanprover/tc) and [trepplein](https://github.com/gebner/trepplein).
We have implemented several kernel extensions to improve performance and make sure the system is reasonably responsive for interactive use.
We strongly recommend you frequently check your project without these extensions. The command line option `-t0` disables all of them.
As far as we know, no proof of `false` has ever been accepted by Lean when using `-t0`.
If you are really concerned about soundness, we recommend you often export your project and recheck it using the independent checkers above.

* Should I open a new issue?

We use [github](https://github.com/leanprover/lean/issues) to track bugs and new features.
Bug reports are always welcome, but nitpicking issues are not (e.g., the error message is confusing).
RFC issues are created by developers only.
