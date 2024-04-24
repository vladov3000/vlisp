static U8  print_buffer[4096];
static U64 print_buffered;

static void flush() {
  if (print_buffered > 0) {
    write(STDOUT_FILENO, print_buffer, print_buffered);
    print_buffered = 0;
  }
}

static void print(String message) {
  if (message.size > sizeof print_buffer) {
    flush();
    write(STDOUT_FILENO, message.data, message.size);
  } else {
    if (message.size > sizeof print_buffer - print_buffered) {
      flush();
    }
    memcpy(&print_buffer[print_buffered], message.data, message.size);
    print_buffered += message.size;
  }
}

static void print_char(U8 c) {
  if (print_buffered == sizeof print_buffer) {
    flush();
  }
  print_buffer[print_buffered] = c;
  print_buffered++;
}

static void print_int(I64 n) {
  U8  buffer[32];
  U8* end      = &buffer[sizeof buffer];
  U8* out      = end;
  B32 negative = n < 0;

  if (negative) {
    n = -n;
  }

  do {
    out--;
    *out = n % 10 + '0';
    n    = n / 10;
  } while (n != 0);

  if (negative) {
    out--;
    *out = '-';
  }

  String message;
  message.data = out;
  message.size = end - out;
  print(message);
}

static void print_float(F64 n) {
  if (n == NAN) {
    print(string("nan"));
    return;
  }
  if (n == INFINITY) {
    print(string("inf"));
    return;
  }
  
  U8  buffer[6];
  U8* end = &buffer[sizeof buffer];
  U8* out = buffer;

  if (n < 0) {
    n = -n;
    print_char('-');
  }

  print_int(n);

  n -= floor(n);

  print_char('.');

  do {
    n *= 10;
    *out = (I64) n % 10 + '0';
    n -= (I64) n;
    out++;
  } while (n > 0.00001 && out != end);

  String message;
  message.data = buffer;
  message.size = out - buffer;
  print(message);
}
