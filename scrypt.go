// Copyright 2012 Dmitry Chestnykh   (Go implementation)
// Copyright 2009 Colin Percival     (original C implementation)
// All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package scrypt implements the scrypt key derivation function as defined in
// Colin Percival's paper "Stronger Key Derivation via Sequential Memory-Hard
// Functions".
package scrypt

import (
	"code.google.com/p/go.crypto/pbkdf2"
	"crypto/sha256"
	"encoding/binary"
	"errors"
)

const maxInt = 1<<31 - 1

// blockCopy copies n bytes from src into dst.
func blockCopy(dst, src []byte, n int) {
	copy(dst, src[:n])
}

// blockXOR XORs bytes from dst with n bytes from src.
func blockXOR(dst, src []byte, n int) {
	for i, v := range src[:n] {
		dst[i] ^= v
	}
}

// salsa applies Salsa20/8 to the given 64-byte slice.
func salsa(b []byte) {
	var w [16]uint32

	for i := 0; i < 16; i++ {
		j := i * 4
		w[i] = uint32(b[j]) | uint32(b[j+1])<<8 | uint32(b[j+2])<<16 | uint32(b[j+3])<<24
	}

	x0, x1, x2, x3, x4, x5, x6, x7, x8 := w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8]
	x9, x10, x11, x12, x13, x14, x15 := w[9], w[10], w[11], w[12], w[13], w[14], w[15]

	for i := 0; i < 8; i += 2 {
		/* Operate on columns. */
		x4 ^= (x0+x12)<<7 | (x0+x12)>>(32-7)
		x8 ^= (x4+x0)<<9 | (x4+x0)>>(32-9)
		x12 ^= (x8+x4)<<13 | (x8+x4)>>(32-13)
		x0 ^= (x12+x8)<<18 | (x12+x8)>>(32-18)

		x9 ^= (x5+x1)<<7 | (x5+x1)>>(32-7)
		x13 ^= (x9+x5)<<9 | (x9+x5)>>(32-9)
		x1 ^= (x13+x9)<<13 | (x13+x9)>>(32-13)
		x5 ^= (x1+x13)<<18 | (x1+x13)>>(32-18)

		x14 ^= (x10+x6)<<7 | (x10+x6)>>(32-7)
		x2 ^= (x14+x10)<<9 | (x14+x10)>>(32-9)
		x6 ^= (x2+x14)<<13 | (x2+x14)>>(32-13)
		x10 ^= (x6+x2)<<18 | (x6+x2)>>(32-18)

		x3 ^= (x15+x11)<<7 | (x15+x11)>>(32-7)
		x7 ^= (x3+x15)<<9 | (x3+x15)>>(32-9)
		x11 ^= (x7+x3)<<13 | (x7+x3)>>(32-13)
		x15 ^= (x11+x7)<<18 | (x11+x7)>>(32-18)

		/* Operate on rows. */
		x1 ^= (x0+x3)<<7 | (x0+x3)>>(32-7)
		x2 ^= (x1+x0)<<9 | (x1+x0)>>(32-9)
		x3 ^= (x2+x1)<<13 | (x2+x1)>>(32-13)
		x0 ^= (x3+x2)<<18 | (x3+x2)>>(32-18)

		x6 ^= (x5+x4)<<7 | (x5+x4)>>(32-7)
		x7 ^= (x6+x5)<<9 | (x6+x5)>>(32-9)
		x4 ^= (x7+x6)<<13 | (x7+x6)>>(32-13)
		x5 ^= (x4+x7)<<18 | (x4+x7)>>(32-18)

		x11 ^= (x10+x9)<<7 | (x10+x9)>>(32-7)
		x8 ^= (x11+x10)<<9 | (x11+x10)>>(32-9)
		x9 ^= (x8+x11)<<13 | (x8+x11)>>(32-13)
		x10 ^= (x9+x8)<<18 | (x9+x8)>>(32-18)

		x12 ^= (x15+x14)<<7 | (x15+x14)>>(32-7)
		x13 ^= (x12+x15)<<9 | (x12+x15)>>(32-9)
		x14 ^= (x13+x12)<<13 | (x13+x12)>>(32-13)
		x15 ^= (x14+x13)<<18 | (x14+x13)>>(32-18)
	}
	w[0] += x0
	w[1] += x1
	w[2] += x2
	w[3] += x3
	w[4] += x4
	w[5] += x5
	w[6] += x6
	w[7] += x7
	w[8] += x8
	w[9] += x9
	w[10] += x10
	w[11] += x11
	w[12] += x12
	w[13] += x13
	w[14] += x14
	w[15] += x15

	j := 0
	for _, v := range w {
		b[j+0] = byte(v >> 0)
		b[j+1] = byte(v >> 8)
		b[j+2] = byte(v >> 16)
		b[j+3] = byte(v >> 24)
		j += 4
	}
}

func blockMix(b, y []byte, r int) {
	x := make([]byte, 64)

	blockCopy(x, b[(2*r-1)*64:], 64)

	for i := 0; i < 2*r; i++ {
		blockXOR(x, b[i*64:], 64)
		salsa(x)

		blockCopy(y[i*64:], x, 64)
	}

	for i := 0; i < r; i++ {
		blockCopy(b[i*64:], y[(i*2)*64:], 64)
	}

	for i := 0; i < r; i++ {
		blockCopy(b[(i+r)*64:], y[(i*2+1)*64:], 64)
	}
}

func integerify(b []byte, r int) uint64 {
	return binary.LittleEndian.Uint64(b[(2*r-1)*64:])
}

func smix(b []byte, r, N int, v, xy []byte) {
	x := xy
	y := xy[128*r:]

	blockCopy(x, b, 128*r)

	for i := 0; i < N; i++ {
		blockCopy(v[i*(128*r):], x, 128*r)
		blockMix(x, y, r)
	}

	for i := 0; i < N; i++ {
		j := int(integerify(x, r) & uint64(N-1))
		blockXOR(x, v[j*(128*r):], 128*r)
		blockMix(x, y, r)
	}

	blockCopy(b, x, 128*r)
}

// Key derives a key from the password, salt and cost parameters, returning a
// byte slice of length keyLen that can be used as cryptographic key.
// 
// N is a CPU/memory cost parameter, must be a power of two greater than 1.
// r and p must satisfy r * p < 2³⁰. If the parameters do not satisfy the
// limits, the function returns a nil byte slice and an error.
//
// For example, you can get a derived key for e.g. AES-256 (which needs a
// 32-byte key) by doing:
//
//      dk := scrypt.Key([]byte("some password"), salt, 16384, 8, 1, 32)
//
// The recommended parameters for interactive logins as of 2009 are N=16384,
// r=8, p=1. They should be increased as memory latency and CPU parallelism
// increases. Remember to get a good random salt.
func Key(password, salt []byte, N, r, p, keyLen int) ([]byte, error) {
	if N <= 1 || N&(N-1) != 0 {
		return nil, errors.New("scrypt: N must be > 1 and a power of 2")
	}
	if uint64(r)*uint64(p) >= 1<<30 || r > maxInt/128/p || r > maxInt/256 || N > maxInt/128/r {
		return nil, errors.New("scrypt: parameters are too large")
	}

	xy := make([]byte, 256*r)
	v := make([]byte, 128*r*N)
	b := pbkdf2.Key(password, salt, 1, p*128*r, sha256.New)

	for i := 0; i < p; i++ {
		smix(b[i*128*r:], r, N, v, xy)
	}

	return pbkdf2.Key(password, b, 1, keyLen, sha256.New), nil
}
