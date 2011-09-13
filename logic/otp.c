/**
    Copyright (c) 2011 Yohanes Nugroho (yohanes@gmail.com)

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.

    The SHA1 code is based on public domain code  by
    Uwe Hollerbach <uh@alumni.caltech edu>
    from Peter C. Gutmann's implementation as found in
    Applied Cryptography by Bruce Schneier
*/
#include "project.h"

#ifdef CONFIG_OTP

#include <string.h>

#include "ports.h"
#include "display.h"
#include "timer.h"
#include "buzzer.h"
#include "user.h"
#include "clock.h"
#include "date.h"

// logic
#include "menu.h"

#include "otp.h"

#undef C

extern struct date sDate;

#define SHA1_BLOCKSIZE     64
#define SHA1_DIGEST_LENGTH 20

/*in this implementation: MAX = 63*/
#define HMAC_KEY_LENGTH 10
#define HMAC_DATA_LENGTH 8

static uint8_t hmac_key[HMAC_KEY_LENGTH];
static uint32_t sha1_digest[8];
static uint32_t sha1_count;
static uint8_t  sha1_data[SHA1_BLOCKSIZE];
static uint32_t sha1_W[80];
static uint8_t hmac_tmp_key[64 + HMAC_DATA_LENGTH];
static uint8_t hmac_sha[SHA1_DIGEST_LENGTH];

// The key for the inner digest is derived from our key, by padding the key
// the full length of 64 bytes, and then XOR'ing each byte with 0x36.


/* SHA f()-functions */
#define f1(x,y,z)    ((x & y) | (~x & z))
#define f2(x,y,z)    (x ^ y ^ z)
#define f3(x,y,z)    ((x & y) | (x & z) | (y & z))
#define f4(x,y,z)    (x ^ y ^ z)

/* SHA constants */
#define CONST1        0x5a827999L
#define CONST2        0x6ed9eba1L
#define CONST3        0x8f1bbcdcL
#define CONST4        0xca62c1d6L

/* truncate to 32 bits -- should be a null op on 32-bit machines */
#define T32(x)    ((x) & 0xffffffffL)

#define R32(x,n)    T32(((x << n) | (x >> (32 - n))))

/* the generic case, for when the overall rotation is not unraveled */
#define FG(n)							\
	T = T32(R32(A,5) + f##n(B,C,D) + E + *WP++ + CONST##n);	\
	E = D; D = C; C = R32(B,30); B = A; A = T


void sha1_transform()
{
	int i;
	uint8_t *dp;
	uint32_t T, A, B, C, D, E,  *WP;

	dp = sha1_data;

#define SWAP_DONE
	for (i = 0; i < 16; ++i) {
		T = *((uint32_t *) dp);
		dp += 4;
		sha1_W[i] =
			((T << 24) & 0xff000000) |
			((T <<  8) & 0x00ff0000) |
			((T >>  8) & 0x0000ff00) | ((T >> 24) & 0x000000ff);
	}

	for (i = 16; i < 80; ++i) {
		sha1_W[i] = sha1_W[i-3] ^ sha1_W[i-8] ^ sha1_W[i-14] ^ sha1_W[i-16];
		sha1_W[i] = R32(sha1_W[i], 1);
	}


	A = sha1_digest[0];
	B = sha1_digest[1];
	C = sha1_digest[2];
	D = sha1_digest[3];
	E = sha1_digest[4];
	WP = sha1_W;
	for (i =  0; i < 20; ++i) { FG(1); }
	for (i = 20; i < 40; ++i) { FG(2); }
	for (i = 40; i < 60; ++i) { FG(3); }
	for (i = 60; i < 80; ++i) { FG(4); }

	sha1_digest[0] = T32(sha1_digest[0] + A);
	sha1_digest[1] = T32(sha1_digest[1] + B);
	sha1_digest[2] = T32(sha1_digest[2] + C);
	sha1_digest[3] = T32(sha1_digest[3] + D);
	sha1_digest[4] = T32(sha1_digest[4] + E);

}

void sha1(const uint8_t* data, uint32_t len, uint8_t digest[20])
{

	int i;

	int count;
	uint32_t lo_bit_count;


	sha1_digest[0] = 0x67452301L;
	sha1_digest[1] = 0xefcdab89L;
	sha1_digest[2] = 0x98badcfeL;
	sha1_digest[3] = 0x10325476L;
	sha1_digest[4] = 0xc3d2e1f0L;
	sha1_count = 0L;

	sha1_count = T32(((uint32_t) len << 3));

	while (len >= SHA1_BLOCKSIZE) {
		memcpy(sha1_data, data, SHA1_BLOCKSIZE);
		data += SHA1_BLOCKSIZE;
		len -= SHA1_BLOCKSIZE;
		sha1_transform();
	}
	memcpy(sha1_data, data, len);

	lo_bit_count = sha1_count;

	count = (int) ((lo_bit_count >> 3) & 0x3f);
	((uint8_t *) sha1_data)[count++] = 0x80;
	if (count > SHA1_BLOCKSIZE - 8) {
		memset(((uint8_t *) sha1_data) + count, 0, SHA1_BLOCKSIZE - count);
		sha1_transform();
		memset((uint8_t *) sha1_data, 0, SHA1_BLOCKSIZE - 8);
	} else {
		memset(((uint8_t *) sha1_data) + count, 0,
		       SHA1_BLOCKSIZE - 8 - count);
	}

	sha1_data[56] = 0;
	sha1_data[57] = 0;
	sha1_data[58] = 0;
	sha1_data[59] = 0;
	sha1_data[60] = (uint8_t)((lo_bit_count >> 24) & 0xff);
	sha1_data[61] = (uint8_t)((lo_bit_count >> 16) & 0xff);
	sha1_data[62] = (uint8_t)((lo_bit_count >>  8) & 0xff);
	sha1_data[63] = (uint8_t)((lo_bit_count >>  0) & 0xff);

	sha1_transform();

	//memcpy(digest, sha1_digest, 20);

	count = 0;
	for(i = 0; i<5; i++) {
		digest[count++] = (unsigned char) ((sha1_digest[i] >> 24) & 0xff);
		digest[count++] = (unsigned char) ((sha1_digest[i] >> 16) & 0xff);
		digest[count++] = (unsigned char) ((sha1_digest[i] >> 8) & 0xff);
		digest[count++] = (unsigned char) ((sha1_digest[i]) & 0xff);
	}

}


//data is in tmp_key + 64
//result is in hmac_sha
uint8_t* hmac_sha1(uint8_t *data) {

	int i;


	// The key for the inner digest is derived from our key, by padding the key
	// the full length of 64 bytes, and then XOR'ing each byte with 0x36.

	for (i = 0; i < HMAC_KEY_LENGTH; ++i) {
		hmac_tmp_key[i] = hmac_key[i] ^ 0x36;
	}
	memset(hmac_tmp_key + HMAC_KEY_LENGTH, 0x36, 64 - HMAC_KEY_LENGTH);

	memcpy(hmac_tmp_key + 64, data, HMAC_DATA_LENGTH);

	sha1(hmac_tmp_key, 64 + HMAC_DATA_LENGTH, hmac_sha);


	// The key for the outer digest is derived from our key, by padding the key
	// the full length of 64 bytes, and then XOR'ing each byte with 0x5C.
	for (i = 0; i < HMAC_KEY_LENGTH; ++i) {
		hmac_tmp_key[i] = hmac_key[i] ^ 0x5C;
	}
	memset(hmac_tmp_key +  HMAC_KEY_LENGTH, 0x5C, 64 - HMAC_KEY_LENGTH);

	memcpy(hmac_tmp_key + 64, hmac_sha, SHA1_DIGEST_LENGTH);

	sha1(hmac_tmp_key, 64 + SHA1_DIGEST_LENGTH, hmac_sha);


	return hmac_sha;
}

static int days[12] ={0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334};

uint32_t simple_mktime(int year, int month, int day, int hour, int minute, int second)
{
	uint32_t	result;

	year += month / 12;
	month %= 12;
	result = (year - 1970) * 365 + days[month];
	if (month <= 1)
		year -= 1;

	//only works for year 2000 - 2032

	result += (year - 1968) / 4;

	result += day -1;

	result = ((result*24+hour)*60+minute)*60 + second;

	return (result);
}

static uint8_t data[] = {0,0,0,0,0,0,0,0};

const char *key = CONFIG_OTP_KEY;

extern struct date sDate;
extern struct time sTime;

static uint32_t last_time = 0;
static uint32_t last_val = 0;

uint32_t otp()
{
	uint32_t val = 0;
	int i;

	uint32_t time = simple_mktime(sDate.year, sDate.month - 1, sDate.day,
				      sTime.hour, sTime.minute, sTime.second);

	time -= CONFIG_OTP_UTC_OFFSET*3600;

	time /= 30;

	if (time==last_time) {
		return last_val;
	}

	memcpy(hmac_key, key, HMAC_KEY_LENGTH);

	last_time = time;

	data[4] = (time >> 24) & 0xff;
	data[5] = (time >> 16) & 0xff;
	data[6] = (time >> 8) & 0xff;
	data[7] = (time) & 0xff;

	hmac_sha1(data);

	int off = hmac_sha[SHA1_DIGEST_LENGTH-1] & 0x0f;

	char *cc = (char *)&val;
	for (i = 0; i < 4; i++) {
		cc[3-i] = hmac_sha[off+i];
	}
	val &= 0x7fffffff;
	val %= 1000000;

	last_val = val;

	return val;
}

static int display_mode = 0; //show first 2 digits

void otp_sx(u8 line)
{
	otp();
	display_otp(line, DISPLAY_LINE_UPDATE_PARTIAL);
}

void otp_switch(u8 line)
{
	display_mode = !display_mode;
	display_otp(line, DISPLAY_LINE_UPDATE_PARTIAL);
}

u8 update_otp(u8 line, u8 update)
{
	otp();
	return 0;
}

#ifdef TEST_SHA1

static char *test_data[] = {
	"abc",
	"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
	"A million repetitions of 'a'"};
static char *test_results[] = {
	"A9993E36 4706816A BA3E2571 7850C26C 9CD0D89D",
	"84983E44 1C3BD26E BAAE4AA1 F95129E5 E54670F1",
	"34AA973C D4C4DAA4 F61EEB2B DBAD2731 6534016F"};

static void hex_p(char *s, int c)
{
	const char *hextab = "0123456789ABCDEF";
	s[0] = hextab[(c >> 4) & 0xf];
	s[1] = hextab[c & 0xf];
}


void digest_to_hex(const uint8_t digest[SHA1_DIGEST_LENGTH], char *output)
{
	int i,j;
	char *c = output;

	for (i = 0; i < SHA1_DIGEST_LENGTH/4; i++) {
		for (j = 0; j < 4; j++) {
			hex_p(c, digest[i*4+j]);
			c += 2;
		}
		*c = ' ';
		c += 1;
	}
	*(c - 1) = '\0';
}

int test_result = 0;

void test_sha1()
{
	int k;
	uint8_t digest[20];
	uint8_t output[80];

	for (k = 0; k < 2; k++){

		sha1(test_data[k], strlen(test_data[k]), digest);
		digest_to_hex(digest, output);
		if (strcmp(output, test_results[k])) {
			test_result = 1;
			break;
		}
	}

}

#endif

void display_otp(u8 line, u8 update)
{

#ifdef TEST_SHA1
	test_sha1();
#endif

	if (update == DISPLAY_LINE_UPDATE_FULL || update == DISPLAY_LINE_UPDATE_PARTIAL)
	{
		u8 *str;

		display_symbol(LCD_ICON_HEART, SEG_ON);

		otp();

		if (!display_mode) {
			display_symbol(LCD_SYMB_MAX, SEG_OFF);
			int v = (last_val / 10000) % 100;
			str = _itoa(v, 2, 0);
			display_chars(LCD_SEG_L2_1_0, str, SEG_ON);
		} else {
			display_symbol(LCD_SYMB_MAX, SEG_ON);
			int v = (last_val % 10000);
			str = _itoa(v, 4, 0);
			display_chars(LCD_SEG_L2_3_0, str, SEG_ON);
		}

#ifdef TEST_SHA1
		if (test_result)
			str = "9999";
		display_chars(LCD_SEG_L2_3_0, str, SEG_ON);
#endif
	}
	if (update == DISPLAY_LINE_CLEAR) {
		display_symbol(LCD_ICON_HEART, SEG_OFF);
		display_symbol(LCD_SYMB_MAX, SEG_OFF);
		display_mode = 0;
	}
}

#endif
