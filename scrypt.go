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
	"crypto/sha256"
	"encoding/binary"
	"errors"

	"code.google.com/p/go.crypto/pbkdf2"
)

const maxInt = 1<<31 - 1

// blockCopy copies n bytes from src into dst.
func blockCopy(dst, src []byte, n int) {
	copy(dst, src[:n])
}

// blockCopyFromArr copies 64 bytes from src array into dst slice.
func blockCopyFromArr(dst []byte, src *[64]byte) {
	copy(dst, src[:])
}

// blockCopyToArr copies 64 bytes from src slice into dst array.
func blockCopyToArr(dst *[64]byte, src []byte) {
	copy(dst[:], src)
}

// blockXOR XORs bytes from dst with n bytes from src.
func blockXOR(dst, src []byte, n int) {
	for i, v := range src[:n] {
		dst[i] ^= v
	}
}

// blockXORToArr XORs 64 bytes from src slice into dst array.
func blockXORToArr(dst *[64]byte, src []byte) {
	for i, v := range src[:64] {
		dst[i] ^= v
	}
}

// salsa applies Salsa20/8 to the given 64-byte slice.
func salsa(b *[64]byte) {
	w0 := uint32(b[0]) | uint32(b[1])<<8 | uint32(b[2])<<16 | uint32(b[3])<<24
	w1 := uint32(b[4]) | uint32(b[5])<<8 | uint32(b[6])<<16 | uint32(b[7])<<24
	w2 := uint32(b[8]) | uint32(b[9])<<8 | uint32(b[10])<<16 | uint32(b[11])<<24
	w3 := uint32(b[12]) | uint32(b[13])<<8 | uint32(b[14])<<16 | uint32(b[15])<<24
	w4 := uint32(b[16]) | uint32(b[17])<<8 | uint32(b[18])<<16 | uint32(b[19])<<24
	w5 := uint32(b[20]) | uint32(b[21])<<8 | uint32(b[22])<<16 | uint32(b[23])<<24
	w6 := uint32(b[24]) | uint32(b[25])<<8 | uint32(b[26])<<16 | uint32(b[27])<<24
	w7 := uint32(b[28]) | uint32(b[29])<<8 | uint32(b[30])<<16 | uint32(b[31])<<24
	w8 := uint32(b[32]) | uint32(b[33])<<8 | uint32(b[34])<<16 | uint32(b[35])<<24
	w9 := uint32(b[36]) | uint32(b[37])<<8 | uint32(b[38])<<16 | uint32(b[39])<<24
	w10 := uint32(b[40]) | uint32(b[41])<<8 | uint32(b[42])<<16 | uint32(b[43])<<24
	w11 := uint32(b[44]) | uint32(b[45])<<8 | uint32(b[46])<<16 | uint32(b[47])<<24
	w12 := uint32(b[48]) | uint32(b[49])<<8 | uint32(b[50])<<16 | uint32(b[51])<<24
	w13 := uint32(b[52]) | uint32(b[53])<<8 | uint32(b[54])<<16 | uint32(b[55])<<24
	w14 := uint32(b[56]) | uint32(b[57])<<8 | uint32(b[58])<<16 | uint32(b[59])<<24
	w15 := uint32(b[60]) | uint32(b[61])<<8 | uint32(b[62])<<16 | uint32(b[63])<<24

	x0, x1, x2, x3, x4, x5, x6, x7, x8 := w0, w1, w2, w3, w4, w5, w6, w7, w8
	x9, x10, x11, x12, x13, x14, x15 := w9, w10, w11, w12, w13, w14, w15

	for i := 0; i < 8; i += 2 {
		u := x0 + x12
		x4 ^= u<<7 | u>>(32-7)
		u = x4 + x0
		x8 ^= u<<9 | u>>(32-9)
		u = x8 + x4
		x12 ^= u<<13 | u>>(32-13)
		u = x12 + x8
		x0 ^= u<<18 | u>>(32-18)

		u = x5 + x1
		x9 ^= u<<7 | u>>(32-7)
		u = x9 + x5
		x13 ^= u<<9 | u>>(32-9)
		u = x13 + x9
		x1 ^= u<<13 | u>>(32-13)
		u = x1 + x13
		x5 ^= u<<18 | u>>(32-18)

		u = x10 + x6
		x14 ^= u<<7 | u>>(32-7)
		u = x14 + x10
		x2 ^= u<<9 | u>>(32-9)
		u = x2 + x14
		x6 ^= u<<13 | u>>(32-13)
		u = x6 + x2
		x10 ^= u<<18 | u>>(32-18)

		u = x15 + x11
		x3 ^= u<<7 | u>>(32-7)
		u = x3 + x15
		x7 ^= u<<9 | u>>(32-9)
		u = x7 + x3
		x11 ^= u<<13 | u>>(32-13)
		u = x11 + x7
		x15 ^= u<<18 | u>>(32-18)

		u = x0 + x3
		x1 ^= u<<7 | u>>(32-7)
		u = x1 + x0
		x2 ^= u<<9 | u>>(32-9)
		u = x2 + x1
		x3 ^= u<<13 | u>>(32-13)
		u = x3 + x2
		x0 ^= u<<18 | u>>(32-18)

		u = x5 + x4
		x6 ^= u<<7 | u>>(32-7)
		u = x6 + x5
		x7 ^= u<<9 | u>>(32-9)
		u = x7 + x6
		x4 ^= u<<13 | u>>(32-13)
		u = x4 + x7
		x5 ^= u<<18 | u>>(32-18)

		u = x10 + x9
		x11 ^= u<<7 | u>>(32-7)
		u = x11 + x10
		x8 ^= u<<9 | u>>(32-9)
		u = x8 + x11
		x9 ^= u<<13 | u>>(32-13)
		u = x9 + x8
		x10 ^= u<<18 | u>>(32-18)

		u = x15 + x14
		x12 ^= u<<7 | u>>(32-7)
		u = x12 + x15
		x13 ^= u<<9 | u>>(32-9)
		u = x13 + x12
		x14 ^= u<<13 | u>>(32-13)
		u = x14 + x13
		x15 ^= u<<18 | u>>(32-18)
	}
	x0 += w0
	x1 += w1
	x2 += w2
	x3 += w3
	x4 += w4
	x5 += w5
	x6 += w6
	x7 += w7
	x8 += w8
	x9 += w9
	x10 += w10
	x11 += w11
	x12 += w12
	x13 += w13
	x14 += w14
	x15 += w15

	b[0], b[1], b[2], b[3] = byte(x0), byte(x0>>8), byte(x0>>16), byte(x0>>24)
	b[4], b[5], b[6], b[7] = byte(x1), byte(x1>>8), byte(x1>>16), byte(x1>>24)
	b[8], b[9], b[10], b[11] = byte(x2), byte(x2>>8), byte(x2>>16), byte(x2>>24)
	b[12], b[13], b[14], b[15] = byte(x3), byte(x3>>8), byte(x3>>16), byte(x3>>24)
	b[16], b[17], b[18], b[19] = byte(x4), byte(x4>>8), byte(x4>>16), byte(x4>>24)
	b[20], b[21], b[22], b[23] = byte(x5), byte(x5>>8), byte(x5>>16), byte(x5>>24)
	b[24], b[25], b[26], b[27] = byte(x6), byte(x6>>8), byte(x6>>16), byte(x6>>24)
	b[28], b[29], b[30], b[31] = byte(x7), byte(x7>>8), byte(x7>>16), byte(x7>>24)
	b[32], b[33], b[34], b[35] = byte(x8), byte(x8>>8), byte(x8>>16), byte(x8>>24)
	b[36], b[37], b[38], b[39] = byte(x9), byte(x9>>8), byte(x9>>16), byte(x9>>24)
	b[40], b[41], b[42], b[43] = byte(x10), byte(x10>>8), byte(x10>>16), byte(x10>>24)
	b[44], b[45], b[46], b[47] = byte(x11), byte(x11>>8), byte(x11>>16), byte(x11>>24)
	b[48], b[49], b[50], b[51] = byte(x12), byte(x12>>8), byte(x12>>16), byte(x12>>24)
	b[52], b[53], b[54], b[55] = byte(x13), byte(x13>>8), byte(x13>>16), byte(x13>>24)
	b[56], b[57], b[58], b[59] = byte(x14), byte(x14>>8), byte(x14>>16), byte(x14>>24)
	b[60], b[61], b[62], b[63] = byte(x15), byte(x15>>8), byte(x15>>16), byte(x15>>24)
}

func blockMix(b, y []byte, r int) {
	var x [64]byte

	blockCopyToArr(&x, b[(2*r-1)*64:])

	for i := 0; i < 2*r; i++ {
		blockXORToArr(&x, b[i*64:])
		salsa(&x)

		blockCopyFromArr(y[i*64:], &x)
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
