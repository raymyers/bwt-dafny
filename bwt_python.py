#!/usr/bin/env python3

def bwt_transform(s):
    """
    Perform Burrows-Wheeler Transform on the input string.
    Returns the transformed string and the index of the original string.
    """
    # Add end-of-string marker if not present
    if '$' not in s:
        s = s + '$'
    
    # Generate all rotations of the input string
    rotations = [s[i:] + s[:i] for i in range(len(s))]
    
    # Sort the rotations lexicographically
    sorted_rotations = sorted(rotations)
    
    # Find the index of the original string in the sorted rotations
    index = sorted_rotations.index(s)
    
    # Extract the last character of each sorted rotation
    transformed = ''.join(rotation[-1] for rotation in sorted_rotations)
    
    return transformed, index

def bwt_inverse(transformed, index):
    """
    Perform inverse Burrows-Wheeler Transform to recover the original string.
    """
    # Create a table with all rotations
    table = [''] * len(transformed)
    
    # Perform len(transformed) iterations
    for i in range(len(transformed)):
        # Insert transformed as the last column
        for j in range(len(transformed)):
            table[j] = transformed[j] + table[j]
        
        # Sort the table
        table.sort()
    
    # Return the original string (the row at the given index)
    return table[index]

def main():
    # Test with "BANANA$"
    input_str = "BANANA$"
    print(f"Input: {input_str}")
    
    transformed, index = bwt_transform(input_str)
    print(f"BWT Transform: {transformed} (index: {index})")
    
    original = bwt_inverse(transformed, index)
    print(f"BWT Inverse: {original}")
    
    # Test with "MISSISSIPPI$"
    input_str = "MISSISSIPPI$"
    print(f"\nInput: {input_str}")
    
    transformed, index = bwt_transform(input_str)
    print(f"BWT Transform: {transformed} (index: {index})")
    
    original = bwt_inverse(transformed, index)
    print(f"BWT Inverse: {original}")

if __name__ == "__main__":
    main()