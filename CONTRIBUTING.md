# Contributing Guidelines

Thank you for your interest in contributing to libssz! Please read the following guidelines to help us review and accept your contributions smoothly.

## How to Submit a Pull Request

1. Fork the repository and create your branch from `main`.
2. Make your changes, following the code style guidelines below.
3. Run checks locally before opening a PR:
   ```sh
   make ci    # or individually: make fmt clippy test test-alloc doc
   ```
4. Open a pull request with a clear, descriptive title.
5. Link related issues if applicable.

## Code Style

- Run `cargo fmt` before committing.
- All `cargo clippy` warnings must be resolved (`-D warnings`).
- Match the existing code style — don't reformat adjacent code.
- Write code in English (comments, names, documentation).

## Testing

- All existing tests must pass: `make test` and `make test-alloc`.
- Add tests for new functionality, including edge cases and error paths.
- Follow existing test patterns in the codebase.
- If your change affects performance, run `make bench` and include results in the PR.

## Commit Signature Verification

All commits must have a verified signature.

- Sign your commits using GPG or SSH so that GitHub marks them as 'Verified'.
- Unsigned or unverified commits may be rejected during review.
- For instructions, see [GitHub: Signing commits](https://docs.github.com/en/authentication/managing-commit-signature-verification/signing-commits).

## Issue Reporting

- Use GitHub Issues to report bugs or request features.
- Include steps to reproduce, expected behavior, and environment details.

## Review Process

- All PRs require review and approval by maintainers.
- You may be asked to make changes before merging.
- Automated checks (fmt, clippy, tests, coverage, `no_std` build) must pass before merge.

## Getting Started: Good First Issues

If you're new to libssz, look for issues labeled ["good first issue"](https://github.com/lambdaclass/libssz/issues?q=state%3Aopen+label%3A%22good+first+issue%22) on GitHub.

If there are no open good first issues at the moment, feel free to browse other issues or open one to ask where to start.

### Contributions Related to Spelling and Grammar

We do not accept PRs from first-time contributors that only address spelling or grammatical errors. For your initial contribution, please focus on meaningful improvements, bug fixes, or new features.

## Contact / Support

- Ask questions by opening an issue on GitHub.

---

We appreciate your help in making libssz better!
