Review the code in ch02. 

I want to revise the sorting algorithms to conform to a new, shared rubric.

See common/CLRS.Common.Complexity.Sorting.Class.fst

I want every sorting algorithm in this chapter to be proven to be an instance of
the array_sort typeclass, parametric in the type of elements and with an instrumented
comparison function tracking ticks.

The goal is to ensure that I don't have to review anything apart from the top-level
instantiation to make sure that the sorting function is correct and has the right
complexity.

Do not add any admits or assumes and do NOT change the Sorting.Class.fst---that is my fixed rubric.

Is the task clear?

There are other agents working in different chapters, so be careful and only
edit files in ch02 and commit only files in this ch02. Commit only
after you confirm that your changes build correctly.

Work in AUTOPILOT MODE. I am not attending to this terminal so make good
decisions and continue working autonomously.
