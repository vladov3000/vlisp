#define true  ((B32) 1)
#define false ((B32) 0)

#define length(array) (sizeof(array) / sizeof((array)[0]))

typedef long long          I64;
typedef unsigned char      U8;
typedef unsigned int       U32;
typedef unsigned long long U64;
typedef double             F64;
typedef U32                B32;

typedef struct {
  U8* data;
  U64 size;
} String;

#define string(s) (String) { .data = (U8*) (s), .size = __builtin_strlen(s) }

static B32 strings_equal(String a, String b) {
  return a.size == b.size && memcmp(a.data, b.data, a.size) == 0;
}
