#############################################
## In order to run the code, copy the files 
## to the sagemath folder
## To execute: ./sage attack.sage.py 
#############################################
from sage.all_cmdline import *   # import sage library

_sage_const_2 = Integer(2); _sage_const_1 = Integer(1); _sage_const_0 = Integer(0); _sage_const_4 = Integer(4); _sage_const_128 = Integer(128); _sage_const_12 = Integer(12); _sage_const_16 = Integer(16); _sage_const_0x3cf2a66e5e175738c9ce521e68361676ff9c508e53b6f5ef1f396139cbd422d9f90970526fd8720467f17999a6456555dda84aa671376ddbe180902535266d383 = Integer(0x3cf2a66e5e175738c9ce521e68361676ff9c508e53b6f5ef1f396139cbd422d9f90970526fd8720467f17999a6456555dda84aa671376ddbe180902535266d383)#!/usr/bin/env sage
from sage.all import *
import struct
import re
from Crypto.Cipher import AES
import sys
from Crypto import Random
key_header = '-----BEGIN PRETTY BAD PUBLIC KEY BLOCK-----\n'
key_footer = '-----END PRETTY BAD PUBLIC KEY BLOCK-----\n'

# Check all indices, return -1 on failure
def brute_force(g, p, t, q):
    for i in range(_sage_const_0 , q):
        if(mod(g**i, p) == mod(t, p)):
            return i
    return -_sage_const_1 

# Chinese remainder theorem ls_pairs: [(a1,m1), (a2,m2)...]
def chinese_remainder(R, ls_pairs, q):
    M = _sage_const_1 
    k = len(ls_pairs)
    S = _sage_const_0 

    # Set M = m1*m2*...*mk
    for pair in ls_pairs:
        M = M * pair[_sage_const_1 ]
    Q = Integers(M)
    for i in range(k):
        M_ = M/ls_pairs[i][_sage_const_1 ]
        m_i = ls_pairs[i][_sage_const_1 ]
        a_i = ls_pairs[i][_sage_const_0 ]
        d,u,v = xgcd(M_, m_i)
        inv = mod(u, m_i)
        S = S + mod(Q(a_i) * Q(M_) * Q(inv), M)
    return R(mod(S, M))


def baby_giant(g, t, p, q):
    m = ceil(sqrt(q))
    lookup = {mod(g**(m*j), p): j for j in xrange(m)}
    for i in range(m):
        x = mod(t*(g**(-i)), p)
        if x in lookup:
            return mod((m*lookup[x] + i), q)
    return -_sage_const_1 
      
def pohlig_hellman(R, q, g, t, pair, p):
    j = _sage_const_0 
    t_j = t
    c = pair[_sage_const_1 ]
    a = []
    while(j <= c-_sage_const_1 ):
        sig = q/(pair[_sage_const_0 ]**(j+_sage_const_1 ))
        delta = mod(t_j**sig, p)
        a_j = R(baby_giant(g**(q/pair[_sage_const_0 ]), delta, p, pair[_sage_const_0 ]))
        if(a_j == -_sage_const_1 ):
            print "Failure in Pohlig hellman"
            return -_sage_const_1 
        a.append(a_j)
        d,u,v = xgcd(g**(a_j*(pair[_sage_const_0 ]**j)), p)
        inv = mod(u,p)
        t_j = mod(t_j*inv, p)
        j = j + _sage_const_1 
    res = R(_sage_const_0 )
    for i in range(len(a)):
        res = res + a[i]*(pair[_sage_const_0 ]**i)
    return R(mod(res, pair[_sage_const_0 ]**pair[_sage_const_1 ]))
    
# Get secret key using pohlig hellman
def get_sec_key(R, g, p, t, q):
    primes = list(factor(p-_sage_const_1 ))
    chinese_rem = []
    i = _sage_const_0 
    for pair in primes:
        a = pohlig_hellman(R, q, g, t, pair, p)
        if(a == -_sage_const_1 ):
            print "Failed"
            return -_sage_const_1 
        chinese_rem.append([a, pair[_sage_const_0 ]**pair[_sage_const_1 ]])
        i = i + _sage_const_1 
        if(i == _sage_const_12 ):
            break
    ans = chinese_remainder(R, chinese_rem, q)
    return ans

def gen_public_key():
    p = _sage_const_0x3cf2a66e5e175738c9ce521e68361676ff9c508e53b6f5ef1f396139cbd422d9f90970526fd8720467f17999a6456555dda84aa671376ddbe180902535266d383 
    R = Integers(p)
    g = R(_sage_const_2 )
    x = ZZ.random_element(_sage_const_2 **_sage_const_128 )
    y = g**x

    key = int_to_mpi(p)+int_to_mpi(g)+int_to_mpi(y)
    print key_header + key.encode('base64') + key_footer
    return key_header + key.encode('base64') + key_footer

# Our "MPI" format consists of 4-byte integer length l followed by l bytes of binary key
def int_to_mpi(z):
    s = int_to_binary(z)
    return struct.pack('<I',len(s))+s

# Horrible hack to get binary representation of arbitrary-length long int
def int_to_binary(z):
    s = ("%x"%z); s = (('0'*(len(s)%_sage_const_2 ))+s).decode('hex')
    return s

# Read one MPI-formatted value beginning at s[index]
# Returns value and index + bytes read.
def parse_mpi(s,index):
    length = struct.unpack('<I',s[index:index+_sage_const_4 ])[_sage_const_0 ]
    z = Integer(s[index+_sage_const_4 :index+_sage_const_4 +length].encode('hex'),_sage_const_16 )
    return z, index+_sage_const_4 +length

# An ElGamal public key consists of a magic header and footer enclosing the MPI-encoded values for p, g, and y.
def parse_public_key(s):
    data = re.search(key_header+"(.*)"+key_footer,s,flags=re.DOTALL).group(_sage_const_1 ).decode('base64')
    index = _sage_const_0 
    p,index = parse_mpi(data,index)
    g,index = parse_mpi(data,index)
    y,index = parse_mpi(data,index)
    return {'p':p, 'g':g, 'y':y}

encrypt_header = '-----BEGIN PRETTY BAD ENCRYPTED MESSAGE-----\n'
encrypt_footer = '-----END PRETTY BAD ENCRYPTED MESSAGE-----\n'

# PKCS 7 pad message.
def pad(s,blocksize=AES.block_size):
    n = blocksize-(len(s)%blocksize)
    return s+chr(n)*n

# Encrypt string s using ElGamal encryption with AES in CBC mode.
# Generate a 128-bit symmetric key, encrypt it using ElGamal, and prepend the MPI-encoded ElGamal ciphertext to the AES-encrypted ciphertext of the message.
def encrypt(pubkey,s):
    p = pubkey['p']; R = Integers(p)
    g = R(pubkey['g']); y = R(pubkey['y'])
    k = ZZ.random_element(_sage_const_2 **_sage_const_128 )
    m = ZZ.random_element(_sage_const_2 **_sage_const_128 )

    output = int_to_mpi(g**k)+int_to_mpi(m*(y**k))
    

    aeskey = int_to_binary(m)
    iv = Random.new().read(AES.block_size)
    
    print (output+iv).encode('base64')
    cipher = AES.new(aeskey, AES.MODE_CBC, iv)

    output += iv + cipher.encrypt(pad(s))

    return encrypt_header + output.encode('base64') + encrypt_footer

def get_aes_key(p, R, q, g, d):
    
    # Get the cipher text. 'cipher' contains the ciphertext without the header and the footer
    # to make my job easier

    ct = open('cipher').read()
    ct = re.search(encrypt_header+"(.*)"+encrypt_footer,ct,flags=re.DOTALL).group(_sage_const_1 ).decode('base64')
    index = _sage_const_0 
    y1, index = parse_mpi(ct,index)
    y2, index = parse_mpi(ct,index)
    y1 = R(y1)
    y2 = R(y2)
    d, u, v = xgcd(y1**d, p)
    m = mod(y2 * u, p)
    aeskey = int_to_binary(m)
    iv = ct[index:index+_sage_const_16 ]
    s = ct[index+_sage_const_16 :]
    cipher = AES.new(aeskey, AES.MODE_CBC, iv)
    output = cipher.decrypt(pad(s))
    return output
    
# Get public key from pubkey.txt
k = open('pubkey.txt').read()
pubkey = parse_public_key(k)
p = pubkey['p']
R = Integers(p)
q = p - _sage_const_1 
g = R(pubkey['g'])
t =  R(pubkey['y'])

# Get secret key
d = get_sec_key(R, g, p, t, q)

f = open('decrypted','w')
f.write(get_aes_key(p, R, q, g, d))
f.close()

