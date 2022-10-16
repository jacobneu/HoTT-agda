# HoTT-agda
Formalization of Homotopy Type Theory in Agda for use in my Youtube videos

This formalization is largely based on the [Agda formalization of HoTT by Egbert Rijke](https://github.com/HoTT-Intro/Agda).
In the Table of Contents below, files marked "Original" are _not_ derived from Egbert's formalization.

All files should be considered "work in progress"; but any lines that appear in a video will be kept as-is, for consistency.

## Table of Contents
### Main files
- `00-preamble.agda`
  - Bookkeeping of universe levels
  - Copy of [`00-preamble.agda`](https://github.com/HoTT-Intro/Agda/blob/master/book/00-preamble.agda)
    - hanged `UU` to `Type`
  - Briefly appears in video No. 2 (optional)
  - To be discussed more in a future video
- `01-simpleTT.agda`
  - Simple type theory: `unit`, `bool`, `empty`, non-dependent products and functions, propositional logic
  - Partially based on [`04-inductive-types.agda`](https://github.com/HoTT-Intro/Agda/blob/master/book/04-inductive-types.agda)
    - Uses `on` and `off` for the names of the booleans, to avoid confusion with propositions-as-types notions of "true" (inhabitedness) and "false" (uninhabitedness)
  - Appears in videos No. 2,3,4

### Examples and Sandboxes
- `exp-square/` (Original)
  - Example of constructive proof in Agda, some annotations of key ideas (`exp-square.agda`). Accompanying library (`lib.agda`).
  - Appears in [video No. 1, Part 3](https://youtu.be/2zcEP2Ny63s)
  - Not connected to main files (self-contained)
- `sandbox-02.agda` (Original)
  - Example of term declaration and computation in Agda (using `Agda.Builtin.String` and `Agda.Builtin.Nat`)
  - Appears in video No. 2
- `sandbox-03.agda` (Original)
  - More `bool` examples (using `Agda.Builtin.String` and `Agda.Builtin.Nat`)
  - Appears in video No. 3
- `sandbox-04.agda` (Original)
  - Toy example with implications, successor function (using `Agda.Builtin.Nat`)
  - Appears in video No. 3
- `example-daysOfWeek.agda` (Original)
  - Example of basic type introduction & pattern-matching. Uses days of the week as example.
  - Appears in video No. 2
- `example-divmod.agda` (Original)
  - Example of using booleans for computation
  - To appear in video No. 3
