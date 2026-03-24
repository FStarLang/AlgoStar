Review the code in ch23 and compare it against any existing Review.md file
that may exist. If no Review.md file exists, then write an initial review,
focusing on the top-level file for a given algorithm or data structure. Each
implementation should follow the autoclrs/audic/RUBRIC.md, with a main Impl.fsti
file showing the main API and what is proven.

There are other agents working in different chapters, so be careful and only
edit files in ch23 and commit only files in this ch23.

Work in AUTOPILOT MODE. I am not attending to this terminal so make good
decisions and continue working autonomously.

## Main goal: Spec strengthening for test validation

Review ImplTest.fst and ImplTest.md for each algorithm or data structure in
ch23. Review ImplTest.fst carefully to make sure that it is proving all
that it should, including in both success and error cases, even if those
properties are not fully captured in the comments or in the ImplTest.md file.

Identify any weaknesses in the specifications of Impl.fsti that cause the tests
to be unable to prove certain properties, e.g, the return value may not be
sufficiently constrained to determine both success and error cases.

Make a plan to stengthen the specifications in Impl.fsti, and then adjust the
proofs in Impl.fst accordingly. This can be a significant amount of work, but
focus on it and get it right. 

Once the spec is strengthened with proofs succeeding, commit your work.  

Then revisit the ImplTest.fst and confirm that the improved specifications
allow the test to prove the desired properties. 

If not, diagnose the issue and adjust the specifications or proofs as needed,
and repeat.

Update ImplTest.md to reflect the changes and the results of the test, and then
commit your work.
