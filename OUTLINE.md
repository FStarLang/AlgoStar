## Outline for AutoCLRS book

Goal: 

A companion to the CLRS text book with formalized proofs and code
implementations for all algorithms in the book.

**WE MUST NOT PLAGIARIZE ANY CONTENT FROM THE CLRS BOOK. **

We will reference the book, as appropriate, and the idea is for a reader to read
our formalization side-by-side with the CLRS book.

The CLRS book itself is available in AutoCLRS in pdf form

We also have the following goals:

* A way for a reader to assess exactly what is proven about each algorithm and
  what is not proven

* A guide to proof techniques used, including specifically how to prove the
  correctness and complexity of algorithms

* More specifically, a companion to the "Proof-oriented Programming in F*" book,
  with a focus on practical applications of the techniques at scale on real
  algorithms, including tips for how to best structure proofs in F* and Pulse,
  common pitfalls, and workarounds.

Format:

Follow the style of the PoP-in-FStar book, available in ../PoP-in-FStar. It uses
restructured text. All code listing are taken from actual implementations in F*
and Pulse, marked up with tags so that we can pull in the fragments we want into
the document---do not copy code listings into the document.

Priority:

Focus on writing chapters for algorithms that are close to ready for detailed
human review.

If an algorithm has many admits, leave it out for now with a placeholder in the
document, and add it back in later when the admits are resolved.


Structure:

Introduction: 
    * Motivation for the book
    * How it was developed: i.e., the process of formalizing the algorithms, writing the proofs, and writing
      the book itself, a collaboration between AI and human authors, and the tools used (F*, Pulse, Markdown, etc.)
        - Describe in particular the mode of interaction between AI and human, the kind of guidance I gave, the parts that you 
          had difficulty with, etc. 

    * Table of contents with a summary of results of each chapter
    * For auditing: A section highlighting gaps in the proofs

The rest of the book will be organized by chapter, following the structure of the CLRS book, with each chapter containing:
    * A subsection for each algorithm
        - A short description of the algorithm with a reference to the relevant part of CLRS
        - A code listing of the F* and Pulse code
           * Include the main statement of correctness of the code
           * Include the main statement of complexity
           * Include any any auxiliary definitions that are necessary to convince oneself that the main statement is correct

        - A summary of the proof techniques used to prove the correctness and complexity of the algorithm,
          with references to the relevant sections of the PoP-in-FStar book for more details on the techniques