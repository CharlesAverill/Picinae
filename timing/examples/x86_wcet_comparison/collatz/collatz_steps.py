def collatz_steps(n):
    """
    Compute the number of steps for n to reach 1 in the Collatz sequence.
    
    Args:
        n (int): Starting number (must be positive integer)
    
    Returns:
        int: Number of steps to reach 1
    """
    if n <= 0:
        raise ValueError("Input must be a positive integer")
    
    steps = 0
    current = n
    
    while current != 1:
        if current % 2 == 0:  # even
            current = current // 2
        else:  # odd
            current = 3 * current + 1
        steps += 1
    
    return steps

# Example usage and testing
if __name__ == "__main__":
    max_steps = 0
    max_val = 0
    for i in range(1, 2**16 - 1):
        if collatz_steps(i) >= max_steps:
            max_steps = collatz_steps(i)
            max_val = i
    print(max_steps, max_val)

