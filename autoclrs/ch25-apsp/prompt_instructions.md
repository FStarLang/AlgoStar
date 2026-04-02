You are working in ch25. There are other agents working in different
chapters, so be careful and only edit files in ch25 and commit only files
in this ch25. Commit only after you confirm that your changes build
correctly.

I have upgraded FStar to use a different branch which will be merged into fstar2
soon. This branch has a revised encoding of universes: you can check the diff in
FStar/src/smtencoding relative to origin/fstar2 to understand the changes.

Now, with this version of F*, there are some warnings and proof regressions in
your chapter ch25. Do a clean build of the chapter and check the warnings
and proof failures.

Use the smtprofiling and proofdebugging skills.

Restore all the proofs and optimize them for use with this branch---lower
rlimits, tighter queries etc.

Also check that the extraction targets work correctly with this branch, use the
krmlextraction skill.

Work in AUTOPILOT MODE. I am not attending to this terminal so make good
decisions and continue working autonomously.

Do not add admits or assumes, do not change any spec in Impl.fsti or
ImplTest.fst
