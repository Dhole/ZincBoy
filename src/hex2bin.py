#!/usr/bin/env python3

import codecs, sys

def num2bits(v, n):
    res = []
    for i in range(n):
        res.append((v >> i) & 1)
    return res
        

bytes = codecs.decode(sys.argv[1], 'hex')
print('  .3...........2 .........1..........0')
print('  1098_7654 32109876 54321098 76543210')
print('0b', end='')
bits = ''.join(['{:08b}'.format(b) for b in bytes[::-1]])
print(f'{bits[0:4]}_{bits[4:8]}_{bits[8:16]}_{bits[16:24]}_{bits[24:32]}')
print()
print('  ',
    '_'.join(['_'.join(map(lambda bit: f'{bit}', num2bits(b, 8)[::-1])) for b in bytes[::-1]]))
