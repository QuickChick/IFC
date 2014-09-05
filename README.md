-- Works with

   + Coq 8.4pl3
   + QuickChick plugin (git@github.com:QuickChick/QuickChick.git)

-- Features 

[TODO:update]
   New features wrt pico-ifc abstract machine:

   - public first-class labels
     + operations producing and/or taking first-class labels:
       Lab, MLab, PcLab, FlowsTo, LJoin, PutBot
   - memory frame labels giving us updatable memory labels
   - brackets
   - registers
     + automatically saved and restored on bracket calls and returns
   - allocation
     (pico-ifc extension; not present in simplest machine)
   - Swiss cheese memory model
     (pico-ifc extension; not present in simplest machine)
     + with additional separation between code and data frames;
       instructions are stored in (read-only) code frames only
   - labels = sets of [pre-allocated] principals
     (pico-ifc extension; not present in simplest machine)

-- Contents
 
[TODO:update]
   Machine      : Definition of the micro-machine # Is it still micro?
   Testing      : Testing infrastructure

-- Compile
   
   make
        This will compile the coq code. Including any "QuickCheck" command 
        will allow you to run tests (inside or outside emacs).

-- Coqtop and lib paths
   
   For Emacs > 23: use directory locals. The example should work:
   
   ln -s example.dir-locals.el .dir-locals.el

-- Misc
   
   * TMU Table is located at Machine/Machine.v, under "fetch_rule"
   * The core of the generation strategy weights is under
     Testing/MachineGen.v, under "ainstr"
   

   
