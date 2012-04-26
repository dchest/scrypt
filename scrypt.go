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

func rot(a, b uint32) uint32 {
	return (a << b) | (a >> (32 - b))
}

// salsa applies Salsa20/8 to the given 64-byte slice.
func salsa(b []byte) {
	var w, x [16]uint32

	for i := 0; i < 16; i++ {
		w[i] = binary.LittleEndian.Uint32(b[i*4:])
	}

	copy(x[:], w[:])

	for i := 0; i < 8; i += 2 {
		/* Operate on columns. */
		x[4] ^= rot(x[0]+x[12], 7)
		x[8] ^= rot(x[4]+x[0], 9)
		x[12] ^= rot(x[8]+x[4], 13)
		x[0] ^= rot(x[12]+x[8], 18)

		x[9] ^= rot(x[5]+x[1], 7)
		x[13] ^= rot(x[9]+x[5], 9)
		x[1] ^= rot(x[13]+x[9], 13)
		x[5] ^= rot(x[1]+x[13], 18)

		x[14] ^= rot(x[10]+x[6], 7)
		x[2] ^= rot(x[14]+x[10], 9)
		x[6] ^= rot(x[2]+x[14], 13)
		x[10] ^= rot(x[6]+x[2], 18)

		x[3] ^= rot(x[15]+x[11], 7)
		x[7] ^= rot(x[3]+x[15], 9)
		x[11] ^= rot(x[7]+x[3], 13)
		x[15] ^= rot(x[11]+x[7], 18)

		/* Operate on rows. */
		x[1] ^= rot(x[0]+x[3], 7)
		x[2] ^= rot(x[1]+x[0], 9)
		x[3] ^= rot(x[2]+x[1], 13)
		x[0] ^= rot(x[3]+x[2], 18)

		x[6] ^= rot(x[5]+x[4], 7)
		x[7] ^= rot(x[6]+x[5], 9)
		x[4] ^= rot(x[7]+x[6], 13)
		x[5] ^= rot(x[4]+x[7], 18)

		x[11] ^= rot(x[10]+x[9], 7)
		x[8] ^= rot(x[11]+x[10], 9)
		x[9] ^= rot(x[8]+x[11], 13)
		x[10] ^= rot(x[9]+x[8], 18)

		x[12] ^= rot(x[15]+x[14], 7)
		x[13] ^= rot(x[12]+x[15], 9)
		x[14] ^= rot(x[13]+x[12], 13)
		x[15] ^= rot(x[14]+x[13], 18)
	}

	for i, v := range w {
		binary.LittleEndian.PutUint32(b[i*4:], v+x[i])
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
// The recommended parameters as of 2009 are N=16384, r=8, p=1. They should be
// increased as memory latency and CPU parallelism increases. Remember to get a
// good random salt. 
func Key(password, salt []byte, N, r, p, keyLen int) ([]byte, error) {
	if N <= 0 || N&(N-1) != 0 {
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
