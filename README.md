# Burrows-Wheeler Transform in Dafny

**This is agent generated code and still likely wrong.**

This repository contains an implementation of the Burrows-Wheeler Transform (BWT) algorithm in Dafny, a programming language designed for formal verification.

## What is the Burrows-Wheeler Transform?

The Burrows-Wheeler Transform is a string transformation algorithm that rearranges a character string into runs of similar characters. This transformation is useful for improving the efficiency of compression algorithms.

## How it Works

The BWT algorithm works as follows:

1. Take a string S of length n and append a special end-of-string character (usually '$')
2. Generate all n rotations of the string
3. Sort these rotations lexicographically
4. Extract the last character of each rotation to form the transformed string
5. Record the index of the original string in the sorted list

To recover the original string, the inverse transform is applied.

## Examples

Input: `BANANA$`
BWT Transform: `ANNB$AA` (index: 4)

Input: `MISSISSIPPI$`
BWT Transform: `IPSSM$PISSII` (index: 5)

## Running the Code

To run the Dafny implementation:

```bash
dafny run -t:py bwt.dfy
```

To run the Python implementation:

```bash
python bwt_python.py
```

## Requirements

- Dafny 4.0.0 or later
- Python 3.6 or later (for the Python implementation)
