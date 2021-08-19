This is a proof of concept implementation of least commitment resolution for CESQ logic, as described in my (Juan Casanova) PhD thesis.

The implementation currently works for small examples, but has computational performance issues for moderately sized ones. Discussions on the reasons and possible solutions for these can be found in my thesis.

This GitHub repository is not currently designed for multiple people contributing, and contains some random tests and only slightly related files. A cleanup would be necessary for proper collaboration, but that is unlikely to happen in the near future.

To look at the code in this repository, the most important files are the following:

-Algorithm.hs: Library with an abstraction of non-deterministic computation procedures that enables defining them, combining them monadically and doing other operations without specifying a search order over the non-deterministic space, as well as running them by specifying a search order. This relies noticeably on the EnumProc.hs library
-AnswerSet.hs: Library with an abstraction of implicit representations of sets that can be used opaquely as if they were explicit representations. Implicit and explicit representations of sets are both combined and masked under the AnswerSet data structure, and functions are given to produce operations on these sets (including operations from implicit to implicit representations) without the need to making the sets explicit until strictly necessary. Relies heavily on Algorithm.hs and EnumProc.hs libraries.
-AutoTests.hs: Simple library with some self-made utilities for performing automated tests.
-CESQLogic.hs: Definition of CESQ logic. Depends on the syntactic definitions on Syntax.hs and the definition of more general query logics in QueryLogic.hs.
-CESQResolverEval.hs: Contains intended moderately sized test examples for the entire algorithm. Unfortunately, most of these do not finish in reasonable times. A lot of them also require slight adaptations to most recent versions of the core algorithm.
-DependencyGraph.hs: One of the main modules of the project. It contains an implementation of the most basic and general aspects of dependency graphs. Most importantly, nodes, edges and equivalence classes.
-EnumProc.hs: Library with a low level abstraction of fair enumeration procedures of infinite search spaces and operations for combining these in multiple ways (including monadically), implementing interleaving, diagonalization and other methods that ensure preservation of fairness of the search.
-Equiv.hs: Small library supporting a data structure for representing equivalence classes.
-ESUnification.hs: One of the main modules of the project. It builds over DependencyGraph.hs to use dependency graphs specifically for the resolution of unification systems of equations. This library contains the rewrite rule system and the normalization of unification dependency graphs.
-ESUnificationTests.hs: Thorough unit test module for ESUnification.hs. These are the most fundamental unit tests in the project.
-GlobalTrace.hs: Small support library for debugging and producing global traces in a simple and unintrusive ways.
-HaskellPlus.hs: Low level library with general extensions to Haskell's standard libraries that I have found useful.
-Heuristics.hs: Small library containing definitions for heuristic procedures and dealing with them monadically.
-Identifier.hs: Support library for handling elements that have an external definition of identity and are managed in non-centralized ways. This is mainly aimed at using them within State monads to find conceptual elements within the state data structure, and to be able to find them in multiple ways.
-MetaLogic.hs: Specific definitions of second-order elements of CESQ logic. Builds on Syntax.hs and ObjectLogic.hs. These are mostly basic definitions of non-parameterized data types and recollection of functions in ESUnification.hs and SOResolution.hs without type parametericity.
-MetaLogicAlpha.hs: Experimental implementation of alpha-equivalence for meta-logic elements. Not currently in use.
-MetaLogicTests.hs: Unit tests for the MetaLogic data structures, including parsing.
-ObjectLogic.hs: Specific definitions of first-order elements of CESQ logic. Builds on Syntax.hs. These are mostly basic definitions of non-parameterized data types and recollection of functions in ESUnification.hs and SOResolution.hs without type parametericity.
-ObjectLogicTests.hs: Unit tests for the ObjectLogic data structures, including parsing.
-Operable.hs: Support library for handling sets of operations with queueing and priorities.
-QueryLogic.hs: General definitions of query logics without the specific particularities of CESQ logic. Mostly, the combination of queries and the handling of implicit representations and parameters.
-Resolution.hs: General abstract notion of a resolution procedure, with monadic application. Would work for first-order resolution, but we use it to build second-order resolution on top of it.
-SOResolution.hs: More specific version of the resolution procedure defined in Resolution.hs which works with the dependency graph unification defined in ESUnification.hs to build a full resolution procedure and enumeration of unification solutions.
-SOResolutionTests.hs: Unit tests for SOResolution.hs. These tests are not automated due to the difficulty in predicting the specific way in which solutions would be produced and the computational difficulty of comparing equivalent solutions a posteriori. Solutions are meant to be checked manually.
-Syntax.hs: Basic library defining syntactic notions such as term structures, second-order terms, substitutions, and normalization at a most abstract level. Used as a fundamental building piece for other modules.
