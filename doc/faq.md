Frequently Asked Questions
==========================

### What is Lean?

Lean is a new open source theorem prover being developed at Microsoft Research.
It is a research project that aims to bridge the gap between interactive and automated theorem proving.
Lean can be also used as a programming language. Actually, some Lean features are implemented in Lean itself.

### Should I use Lean?

Lean is under heavy development, and we are constantly trying new
ideas and tweaking the system.  It is a research project and not a product.
Things change rapidly, and we constantly break backward compatibility.
Lean comes "as is", you should not expect we will fix bugs and/or add new features for your project.
We have our own priorities, and will not change them to accommodate your needs.
Even if you implement a new feature or fix a bug, we may not want to merge it because
it may conflict with our plans for Lean, it may not be performant, we may not want to maintain it,
we may be busy, etc. If you really need this new feature or bug fix, we suggest you create your own fork and maintain it yourself.

### Where is the documentation?

This is the Lean 4 manual. It is a work in progress, but it will eventually cover the whole language.
A public and very active chat room dedicated to Lean is open on [Zulip](https://leanprover.zulipchat.com).
It is a good place to interact with other Lean users.

### Should I use Lean to teach a course?

Lean has been used to teach courses on logic, type theory and programming languages at CMU and the University of Washington.
The lecture notes for the CMU course [Logic and Proof](https://lean-lang.org/logic_and_proof) are available online,
but they are for Lean 3.
If you decide to teach a course using Lean, we suggest you prepare all material before the beginning of the course, and
make sure that Lean attends all your needs. You should not expect we will fix bugs and/or add features needed for your course.

### Are there IDEs for Lean?

Yes, see [Setting Up Lean](./setup.md).

### Is Lean sound? How big is the kernel? Should I trust it?

Lean has a relatively small kernel.
Several independent checkers have been implemented for Lean 3. Two of them are
[tc](https://github.com/leanprover/tc) and [trepplein](https://github.com/gebner/trepplein).
We expect similar independent checkers will be built for Lean 4.

### Should I open a new issue?

We use [GitHub](https://github.com/leanprover/lean4/issues) to track bugs and new features.
Bug reports are always welcome, but nitpicking issues are not (e.g., the error message is confusing).
See also our [contribution guidelines](https://github.com/leanprover/lean4/blob/master/CONTRIBUTING.md).

### Is it Lean, LEAN, or L∃∀N?

We always use "Lean" in writing.
When specifying a major version number, we append it together with a single space: Lean 4.
