Review the code in ch26. I want to compile the ImplTest.fst file and all
its dependences to C, run it, and check that the expected test output is
correct. If there are other, older test files in the chapter, you can ignore
them. Focus on ImplTest.fst and its dependencies. 

You should use AutoCLRS/krml/karamel/krml for this.

Look at ~/ws2/FunFm/verif/csrc/Makefile for how to extract Pulse code to C, via
krml. Note, in particular, the use of the bundle options. Also review
$(PULSE_ROOT)/mk/test.mk for insights on how to write test targets.

Add an extract and test target to the Makefile in ch26 that extracts the
code to C, compiles it, and runs it. Based on your findings, update ImplTest.md
with your status of concrete execution results

Note: In order to compile to C, all the reachable code from ImplTest.fst must be
compilable to C naturally. In particular, 

* make sure you fix warnings about deprecation of R.alloc, R.free, A.alloc,
  A.free and use let mut instead.

* Use the bundle options of krml to make sure that only things reachable from
  ImplTest.fst are extracted. It might be useful to write an ImplTest.fsti for
  this purpose, with only the signature of the main test function there.

* unbounded datatypes like list etc. should not appear in the code to be
  extracted. They can of course appear in specs, but in code to be extracted,
  they should be not used at all, or appear only as erased list, etc. 

There are other agents working in different chapters, so be careful and only
edit files in ch26 and commit only files in this ch26. Commit only
after you confirm that your changes build correctly.

Work in AUTOPILOT MODE. I am not attending to this terminal so make good
decisions and continue working autonomously.

Do not add admits or assumes, do not change any spec in Impl.fsti or
ImplTest.fst
