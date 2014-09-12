IFC Experiments with QuickChick
===============================

## Description
  - Information Flow Control (IFC) case study using the QuickChick
    testing plugin for Coq. Includes verification of testing and some
    other Coq proofs (see below).

## Prerequisites
  - Known to work with Coq 8.4pl4
  - QuickChick plugin (https://github.com/QuickChick/QuickChick)

## Contents
  - Information-flow machine (http://arxiv.org/abs/1409.0393)
    * Labels.v, Lab2.v, Lab4.v, LabSetsOfPrins.v
    * Instructions.v, Memory.v, Rules.v, Machine.v
  - Testing code
    * Driver.v -- runs the tests
    * TestingCommon.v, Generation.v, Shrinking.v, Printing.v
    * Indist.v, Reachability.v, SanityChecks.v, SSNI.v
    * Mutate.v -- generating mutants for mutation testing
  - Testing verification proofs    
    * GenerationProofsHelpers.v
    * GenerationProofs.v -- CH: broken since 2f9d25043cf
    * SSNICheckerProofs.v -- CH: broken since 2f9d25043cf
  - Noninterference proofs
    * NotionsOfNI.v -- proofs relating various noninterference notions
    * NIProof.v -- a still unfinished noninterference proof
    * Indist.v -- the indistinguishability relation
  - An experiment with representing IFC rules inductively
    (requires relation extraction Coq plugin:
     https://github.com/picnic/RelationExtraction)
    * RelationExtraction.v

## Compiling

    make

## Compiling and running tests

    make && coqc Driver.v

## License
  - The files in this directory are distributed under the MIT license
    (see LICENSE)
  - The files in the compcert/lib directory are dual-licensed under
    the INRIA Non-Commercial License Agreement and the GNU General
    Public License version 2 or later (see compcert/LICENSE)
