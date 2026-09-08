# Jordan criterion for a free associative algebra

This directory contains a Wolfram Language implementation of the polynomial
criterion of F. A. Mashurov and B. K. Sartayev for deciding whether a
multilinear associative polynomial is a Jordan element.

## Files

- JordanCriterion.wl - the version-controlled source code. This is the file
  to review, cite, and edit.
- JordanCriterionDemo.nb - a small interactive Mathematica notebook that
  loads the source file and runs the verified degree-3, degree-4, and degree-5
  examples.

The implementation was tested with Wolfram Mathematica 14.0.0 for macOS ARM.

## Important correction from the earlier notebook

The earlier Jordan_criterion.nb searched a coefficient list with
FirstPosition[..., Except[0], {1}, 1]. In Mathematica 14 this can match the
head List at position {0}. As a result,
JordanCharacteristicPolynomial[n, t] returned the impossible value
e_n = -1 and made q_n one degree too large.

This version uses LengthWhile to count the initial zero coefficients. Its
self-test checks both invariants

~~~text
e_n = nullity(U_n)
deg(q_n) = rank(U_n)
~~~

for every degree from 1 through 5, so the defect cannot silently recur.

For dimensions up to 120 (that is, through degree 5), the minimal polynomial is
now computed deterministically as the monic square-free part of the exact
characteristic polynomial. Larger degrees retain the Krylov method with exact
rational coefficient recovery and repeated validation.

String parsing no longer calls ToExpression. It accepts only the documented
integer/rational syntax, validates every permutation, rejects nonlinear input,
and rejects inexact decimal coefficients.

## Quick start in Mathematica

Put JordanCriterion.wl and JordanCriterionDemo.nb in the same directory.
Open the demo notebook and choose **Evaluation > Evaluate Notebook**.

To work directly from a fresh Mathematica notebook:

~~~wl
Get["/absolute/path/to/JordanCriterion.wl"];
JordanSelfTest[]
~~~

The final output should be:

~~~text
ALL TESTS PASSED
True
~~~

Restart the kernel before loading a newly downloaded revision. This prevents
old memoized matrices or polynomials from an earlier version remaining in the
session.

## Verified runs

The following are the same sample inputs used for the checked runs:

~~~wl
r3 = JordanReport[
  3,
  "123 + 321",
  ShowMatrix -> False,
  ComputeQ -> True
];

r4 = JordanReport[
  4,
  "1234 + 4321 + 1243 + 3421",
  ShowMatrix -> False,
  ComputeQ -> True
];

r5 = JordanReport[
  5,
  "12345 + 54321",
  ShowMatrix -> False,
  ComputeQ -> True
];
~~~

Expected summaries:

| n | dim V_n | e_n | dim(J intersect V_n) | deg p_n | deg q_n | sample verdict |
|---:|---:|---:|---:|---:|---:|:---|
| 3 | 6 | 3 | 3 | 2 | 3 | Jordan |
| 4 | 24 | 13 | 11 | 5 | 11 | Jordan |
| 5 | 120 | 65 | 55 | 12 | 55 | not Jordan |

The degree-5 verdict applies to the displayed reverse pair
12345 + 54321; it does not say that every degree-5 polynomial is non-Jordan.

## Entering a polynomial

For degrees at most 9, the compact string form is convenient:

~~~wl
JordanElementQ[4, "1234 + 4321"]
JordanElementQ[4, "3*1234 - 2*1243 + 7/5*4321"]
~~~

You can also use symbolic word notation:

~~~wl
f = w[1234] + w[4321] + w[1243] + w[3421];
JordanElementQ[4, f]
~~~

or a list of rules:

~~~wl
f = {
  {1, 2, 3, 4} -> 1,
  {4, 3, 2, 1} -> 1
};
JordanElementQ[4, f]
~~~

For degree 10 and above, use lists because a decimal digit cannot encode the
letter label 10:

~~~wl
w[{1, 2, 3, 4, 5, 6, 7, 8, 9, 10}]
~~~

Use exact coefficients (1/2, not 0.5). Exact equality is essential to the
membership test.

## Main commands

~~~wl
JordanElementQ[n, f]          (* True or False *)
JordanReport[n, f]            (* printed calculation plus an Association *)
JordanCriterionPolynomial[n]  (* p_n(t) *)
JordanMinimalPolynomial[n]    (* m_n(t) *)
JordanCharacteristicPolynomial[n]
JordanU[n]                    (* exact n! by n! matrix *)
JordanProject[n, f]           (* f Pi_n *)
JordanExpression[n, f]        (* explicit Jordan-monomial data *)
JordanDimension[n]
JordanSelfTest[]
~~~

JordanReport accepts these options:

~~~wl
ShowMatrix -> Automatic
MaxTerms -> 24
ComputeQ -> Automatic
ShowJordanExpression -> False
~~~

The older string option names, such as "ShowMatrix" -> False, remain accepted
for compatibility. New code should use the symbol form shown above.

The returned Association stores the full vectors even when long printed
expressions are suppressed.

## Uploading to GitHub

### GitHub website

1. Create or open the repository.
2. Choose **Add file > Upload files**.
3. Upload JordanCriterion.wl, JordanCriterionDemo.nb, and README.md.
4. Use a commit message such as: Add verified Mathematica Jordan criterion.
5. After the repository URL is stable, replace the [?] implementation
   placeholder in the paper with a link to the repository or to
   JordanCriterion.wl.

### Command line

From the repository directory:

~~~bash
git add JordanCriterion.wl JordanCriterionDemo.nb README.md
git commit -m "Add verified Mathematica Jordan criterion"
git push
~~~

Before every release, run JordanSelfTest[] in a fresh Mathematica kernel and
confirm that it ends with ALL TESTS PASSED.
