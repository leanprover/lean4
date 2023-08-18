External Contribution Guidelines
============

**In the past, we accepted most pull requests. This practice produced hard to maintain code, performance problems, and bugs.** In order to improve the quality and maintainability of our codebase, we've established the following guidelines for external contributions.

Before You Submit a Pull Request (PR):
-------

**Start with an Issue**: Before submitting a PR, always open an issue discussing the problem you wish to solve or the feature you'd like to add. Use the prefix `RFC:` (request for comments) if you are proposing a new feature. Ask for feedback from other users. Take the time to summarize all the feedback. This allows the maintainers to evaluate your proposal more efficiently. When creating a RFC, consider the following questions:

  - **User Experience**: How does this feature improve the user experience?

  - **Beneficiaries**: Which Lean users and projects do benefit most from this feature/change?

  - **Community Feedback**: Have you sought feedback or insights from other Lean users?

  - **Maintainability**: Will this change streamline code maintenance or simplify its structure?

**Understand the Project**: Familiarize yourself with the project, existing issues, and latest commits. Ensure your contribution aligns with the project's direction and priorities.

**Stay Updated**: Regularly fetch and merge changes from the main branch to ensure your branch is up-to-date and can be smoothly integrated.

**Help wanted**: We have issues tagged with ["help wanted"](https://github.com/leanprover/lean4/issues?q=is%3Aissue+is%3Aopen+label%3A%22help+wanted%22), if you want to contribute to the project, please take a look at them. If you are interested in one of them, post comments, ask questions, and engage with the core developers there.

Quality Over Quantity:
-----

**Focused Changes**: Each PR should address a single, clearly-defined issue or feature. Avoid making multiple unrelated changes in a single PR.

**Write Tests**: Every new feature or bug fix should come with relevant tests. This ensures the robustness and reliability of the contribution.

**Documentation**: Update relevant documentation, including comments in the code, to explain the logic and reasoning behind your changes.

Coding Standards:
----

**Follow the Code Style**: Ensure that your code follows the established coding style of the project.

**Lean on Lean**: Use Lean's built-in features and libraries effectively, avoiding reinventions.

**Performance**: Make sure that your changes do not introduce performance regressions. If possible, optimize the solution for speed and resource usage.

PR Submission:
---

**Descriptive Title and Summary**: The PR title should briefly explain the purpose of the PR. The summary should give more detailed information on what changes are made and why. Links to Zulip threads are not acceptable as a summary. You are responsible for summarizing the discussion, and getting support for it.

**Link to Relevant Issues**: Reference any issues that your PR addresses to provide context.

**Stay Responsive**: Once the PR is submitted, stay responsive to feedback and be prepared to make necessary revisions. We will close any PR that has been inactive (no response or updates from the submitter) for more than a month.

Reviews and Feedback:
----

**Be Patient**: Given the limited number of full-time maintainers and the volume of PRs, reviews may take some time.

**Engage Constructively**: Always approach feedback positively and constructively. Remember, reviews are about ensuring the best quality for the project, not personal criticism.

**Continuous Integration**: Ensure that all CI checks pass on your PR. Failed checks will delay the review process. The maintainers will not check PRs containing failures.

What to Expect:
----

**Not All PRs Get Merged**: While we appreciate every contribution, not all PRs will be merged. Ensure your changes align with the project's goals and quality standards.

**Feedback is a Gift**: It helps improve the project and can also help you grow as a developer or contributor.

**Community Involvement**: Engage with the Lean community on our communication channels. This can lead to better collaboration and understanding of the project's direction.
