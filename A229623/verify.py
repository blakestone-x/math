"""Enumerate palindromes from prefixes, then check both digit-sum classifications."""
from itertools import product


def value(digits, base):
    number = 0
    for digit in digits:
        number = number * base + digit
    return number


def palindrome(number, base):
    current, reverse = number, 0
    while current:
        current, digit = divmod(current, base)
        reverse = reverse*base+digit
    return number == reverse


def enumerate_length(base, length):
    half = (length+1)//2
    for first in range(1, base):
        for tail in product(range(base), repeat=half-1):
            prefix = (first, *tail)
            mirrored = prefix[:-1] if length % 2 else prefix
            digits = prefix+mirrored[::-1]
            yield value(digits, base), sum(digits)


def subtraction():
    small = [0]
    examined = 0
    for base in range(2, 13):
        for length in range(1, 17):
            if (base-1)*base**((length-1)//2) > 100_000:
                break
            matches = []
            for number, digit_sum in enumerate_length(base, length):
                examined += 1
                if palindrome(number-digit_sum, base):
                    matches.append(number)
                if base == 10 and 4 <= length <= 9:
                    assert not palindrome(number+digit_sum, base)
            if base == 10 and length < 4:
                small.extend(matches)
            if length >= 6 or (base == 10 and length >= 4):
                expected = [base**(length-1)+1]
                if base % 2:
                    expected.append((base+1)//2 * expected[0])
                assert matches == expected, (base, length, matches)
    assert small == [*range(10),11,101,181,262,343,424,686,767,848,929]
    return examined


def addition():
    first = []
    for j in range(1, 4):
        count = 0
        for w in range(10**j+1, 10**(j+1)):
            if w % 9 != 2 or w % 10 == 0:
                continue
            total = sum(map(int, str(w)))
            c, rem = divmod(11*10**j-2*(total-1), 9)
            assert rem == 0 and c > 0
            lower, upper = str(w-1), str(w)
            number = int(lower + "9"*c + lower[::-1])
            target = int(upper + "0"*c + upper[::-1])
            assert number + sum(map(int, str(number))) == target
            if j == 1:
                first.append(number)
            count += 1
        assert count == 9*10**(j-1)
    assert sorted(first) == [
        28999999999982,37999999999973,46999999999964,55999999999955,
        64999999999946,73999999999937,82999999999928,91999999999919,
        1099999999999901]


if __name__ == "__main__":
    examined = subtraction()
    addition()
    print(f"Checked {examined:,} palindromes in bases 2 through 12 and 999 addition witnesses.")
