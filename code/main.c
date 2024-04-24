#include <assert.h>
#include <fcntl.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

#include "basic.h"
#include "print.h"

static String read_file(char* path) {
  int fd = open(path, O_RDONLY);
  assert(fd != -1);

  struct stat info;
  assert(fstat(fd, &info) == 0);

  U64 size = info.st_size;
  U8* data = mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
  return (String) { .data = data, .size = size };
}

typedef struct {
  U8* memory;
  U64 used;
  U64 committed;
} Arena;

static void arena_initialize(Arena* arena, U64 capacity) {
  U8* memory = mmap(NULL, capacity, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  assert(memory != MAP_FAILED);

  arena->memory	   = memory;
  arena->used	   = 0;
  arena->committed = 0;
}

static U8* arena_allocate_bytes(Arena* arena, U64 size, U64 alignment) {
  U8* memory	= arena->memory;
  U64 used	= arena->used;
  U64 committed = arena->committed;
  U8* result;

  used   = (used + alignment - 1) & ~(alignment - 1);
  result = &memory[used];
  used   = used + size;

  if (used > committed) {
    U64 new = (used - committed + 4095) & ~(4095);
    assert(mprotect(&memory[committed], new, PROT_READ | PROT_WRITE) == 0);
    committed += new;
  }

  arena->used      = used;
  arena->committed = committed;
  return result;
}

#define arena_allocate(arena, type) \
  ((type*) arena_allocate_bytes(arena, sizeof(type), _Alignof(type)))

typedef struct Values Values;

typedef enum {
  TERM_STRING,
  TERM_INTEGER,
  TERM_NUMBER,
  TERM_ATOM,
  TERM_LIST,
  TERM_BUILT_IN,
  TERM_PROCEDURE,
} TermKind;

typedef struct Term Term;

typedef struct {
  Term* head;
  Term* tail;
} List;

typedef String Atom;

typedef struct {
  String  name;
  Values* captured;
  Term*   parameters;
  Term*   body;
} Procedure;

struct Term {
  TermKind kind;
  union {
    String    string;
    I64       integer;
    F64       number;
    Atom      atom;
    List      list;
    U64       built_in;
    Procedure procedure;
  };
};

static Term term_nil = {
  .kind = TERM_LIST,
};

static Term term_t = {
  .kind = TERM_ATOM,
  .atom = string("t"),
};

static B32 is_nil_term(Term* term) {
  return term->kind == TERM_LIST && term->list.head == NULL && term->list.tail == NULL;
}

typedef struct {
  Term*   term;
  Values* values;
} EvaluateResult;

static void print_term(Term* term);
static EvaluateResult evaluate_term(Arena* arena, Values* values, Term* input);

#include "built_in.h"

static void print_term(Term* term) {
  switch (term->kind) {

  case TERM_ATOM:
    print(term->atom);
    break;

  case TERM_STRING: {
    String string = term->string;
    print_char('"');
    for (U64 i = 0; i < string.size; i++) {
      U8 c = string.data[i];
      if (c == '\n') {
	print(string("\\n"));
      } else if (c == '\\') {
	print(string("\\\\"));
      } else {
	print_char(string.data[i]);
      }
    }
    print_char('"');
    break;
  }

  case TERM_INTEGER:
    print_int(term->integer);
    break;

  case TERM_NUMBER:
    print_float(term->number);
    break;

  case TERM_LIST:
    print_char('(');
    Term* current = term;
    while (current->list.head != NULL && current->list.tail != NULL) {
      if (current != term) {
	print_char(' ');
      }
      print_term(current->list.head);
      current = current->list.tail;
    }
    print_char(')');
    break;

  case TERM_BUILT_IN:
    print(string("<built_in_"));
    print(built_in_names[term->built_in]);
    print_char('>');
    break;

  case TERM_PROCEDURE: {
    Procedure* procedure = &term->procedure;
    print_char('<');
    print(procedure->name);
    for (Term* i = procedure->parameters; i->list.head && i->list.tail; i = i->list.tail) {
      print_char(' ');
      print(i->list.head->atom);
    }
    print_char('>');
    break;
  }
  };
}

static B32 is_space(U8 c) {
  return c == ' ' || c == '\n' || c == '\t';
}

static B32 is_digit(U8 c) {
  return '0' <= c && c <= '9';
}

typedef enum {
  TOKEN_END,
  TOKEN_LPAREN,
  TOKEN_RPAREN,
  TOKEN_STRING,
  TOKEN_INTEGER,
  TOKEN_NUMBER,
  TOKEN_ATOM,
} TokenKind;

typedef struct {
  TokenKind kind;
  String    token;
  I64       integer;
  F64       number;
  String    rest;
} LexResult;

static String clear_blanks(String input) {
 START:
  while (input.size > 0 && is_space(*input.data)) {
    input.data++;
    input.size--;
  }

  if (input.size > 0 && *input.data == ';') {
    while (input.size > 0 && *input.data != '\n') {
      input.data++;
      input.size--;
    }
    goto START;
  }
  
  return input;
}

LexResult lex(Arena* arena, String input) {
  input = clear_blanks(input);

  TokenKind kind    = TOKEN_END;
  String    token   = { .data = input.data, .size = 0 };
  I64       integer = 0;
  F64       number  = 0;

  if (input.size > 0) {
    if (*input.data == '(' || *input.data == ')') {
      kind = *input.data == '(' ? TOKEN_LPAREN : TOKEN_RPAREN;
      input.data++;
      input.size--;
    } else if (*input.data == '"') {
      kind = TOKEN_STRING;
      input.data++;
      input.size--;
      B32 escaped = false;

      token.data = arena_allocate_bytes(arena, 0, 1);
      
      while (input.size > 0 && *input.data != '"') {
	if (escaped) {
	  assert(*input.data == '\\' || *input.data == 'n');
	  *arena_allocate_bytes(arena, 1, 1) = *input.data == '\\' ? '\\' : '\n';
	  token.size++;
	  escaped = false;
	} else if (*input.data == '\\') {
	  escaped = true;
	} else {
	  *arena_allocate_bytes(arena, 1, 1) = *input.data;
	  token.size++;
	}
	input.data++;
	input.size--;	
      }
      assert(input.size > 0);
      input.data++;
      input.size--;      
    } else if (is_digit(*input.data) ||
	       (*input.data == '-' && input.size > 0 && is_digit(input.data[1]))) {
      B32 negative = *input.data == '-';
      if (negative) {
	input.data++;
	input.size--;
      }
		 
      kind = TOKEN_INTEGER;
      while (input.size > 0 && is_digit(*input.data)) {
	U8 digit = *input.data - '0';
	assert(integer < (0x7FFFFFFFFFFFFFFFll - digit) / 10);
	integer  = integer * 10 + digit;
	input.data++;
	input.size--;
      }
      if (input.size > 0 && *input.data == '.') {
	input.data++;
	input.size--;
	kind      = TOKEN_NUMBER;
	number    = integer;
	U64 count = 1;
	while (input.size > 0 && is_digit(*input.data)) {
	  U8 digit = *input.data - '0';
	  number += digit / pow(10, count);
	  input.data++;
	  input.size--;
	  count++;
	}
	if (negative) {
	  number = -number;
	}
      } else {
	if (negative) {
	  integer = -integer;
	}
      }
    } else {
      kind = TOKEN_ATOM;
      while (input.size > 0 && !is_space(*input.data) && *input.data != '(' && *input.data != ')') {
	input.data++;
	input.size--;
      }
    }
  }
  if (token.size == 0) {
    token.size = input.data - token.data;
  }

  LexResult result;
  result.kind    = kind;
  result.token   = token;
  result.integer = integer;
  result.number  = number;
  result.rest    = input;
  return result;
}

typedef struct {
  Term*  term;
  String rest;
} ParseResult;

ParseResult parse(Arena* arena, String input) {
  LexResult lexed = lex(arena, input);
  input           = lexed.rest;

  Term* term;
  if (lexed.kind == TOKEN_LPAREN) {
    Term* first      = NULL;
    Term* last       = NULL;
    
    Term* nil      = arena_allocate(arena, Term);
    nil->kind      = TERM_LIST;
    nil->list.head = NULL;
    nil->list.tail = NULL;

    while (input.size > 0 && *input.data != ')') {
      ParseResult parsed = parse(arena, input);
      input              = parsed.rest;
      
      Term* new      = arena_allocate(arena, Term);
      new->kind      = TERM_LIST;
      new->list.head = parsed.term;
      new->list.tail = nil;
      
      if (first == NULL) {
	first = new;
	last  = new;
      } else {
	last->list.tail = new;
	last            = new;
      }
      input = clear_blanks(input);
    }
    assert(input.size > 0);
    input.data++;
    input.size--;
    term = first;
  } else if (lexed.kind == TOKEN_STRING) {
    term         = arena_allocate(arena, Term);
    term->kind   = TERM_STRING;
    term->string = lexed.token;
  } else if (lexed.kind == TOKEN_INTEGER) {
    term          = arena_allocate(arena, Term);
    term->kind    = TERM_INTEGER;
    term->integer = lexed.integer;
  } else if (lexed.kind == TOKEN_NUMBER) {
    term         = arena_allocate(arena, Term);
    term->kind   = TERM_NUMBER;
    term->number = lexed.number;
  } else if (lexed.kind == TOKEN_ATOM) {
    term       = arena_allocate(arena, Term);
    term->kind = TERM_ATOM;
    term->atom = lexed.token;
  } else {
    assert(lexed.kind != TOKEN_END);
    assert(lexed.kind != TOKEN_RPAREN);
  }

  ParseResult result;
  result.term = term;
  result.rest = input;
  return result;
}

typedef struct Values Values;

struct Values {
  String  name;
  Term*   value;
  Values* next;
};

static Term* find_value(Values* values, String name) {
  for (Values* i = values; i != NULL; i = i->next) {
    if (strings_equal(name, i->name)) {
      return i->value;
    }
  }
  return NULL;
}

static Term* make_procedure(
  Arena* arena, Values* values, String name, Term* parameters, Term* body
) {
  for (Term* i = parameters; i->list.head && i->list.tail; i = i->list.tail) {
    assert(i->list.head->kind == TERM_ATOM);
  }
	
  Term* value = arena_allocate(arena, Term);
  value->kind = TERM_PROCEDURE;
	
  Procedure* procedure  = &value->procedure;
  procedure->name       = name;
  procedure->captured   = values;
  procedure->parameters = parameters;
  procedure->body       = body;
  assert(procedure->body != NULL);
  return value;
}

static EvaluateResult evaluate_term(Arena* arena, Values* values, Term* input) {
  Term* output;

  switch (input->kind) {

  case TERM_STRING:
  case TERM_INTEGER:
  case TERM_NUMBER:
    output  = arena_allocate(arena, Term);
    *output = *input;
    break;

  case TERM_ATOM: {
    Term* value = find_value(values, input->atom);
    if (value == NULL) {
      print(string("Undefined value "));
      print(input->atom);
      print(string(".\n"));
      exit(EXIT_FAILURE);
    }
    output  = arena_allocate(arena, Term);
    *output = *value;
    break;
  }

  case TERM_LIST:
    assert(input->list.head != NULL && input->list.tail != NULL);
    Term* head = input->list.head;
    if (head->kind == TERM_ATOM && strings_equal(head->atom, string("let"))) {
      input = input->list.tail;
      assert(!is_nil_term(input));
      Term*   bindings   = input->list.head;
      assert(input->list.tail->kind == TERM_LIST && !is_nil_term(input->list.tail));
      Term*   body       = input->list.tail->list.head;
      Values* new_values = values;
      for (Term* i = bindings; !is_nil_term(i); i = i->list.tail) {
	assert(i->kind == TERM_LIST);
	Term* binding = i->list.head;
	assert(binding->kind == TERM_LIST && !is_nil_term(binding));
	assert(binding->list.tail->kind == TERM_LIST && !is_nil_term(binding->list.tail));
	Term* name    = binding->list.head;
	assert(name->kind == TERM_ATOM);
	Term* value = evaluate_term(arena, values, binding->list.tail->list.head).term;
	
	Values* new = arena_allocate(arena, Values);
	new->name   = name->atom;
	new->value  = value;
	new->next   = new_values;
	new_values  = new;
      }
      return evaluate_term(arena, new_values, body);
    } if (head->kind == TERM_ATOM && strings_equal(head->atom, string("lambda"))) {
      input = input->list.tail;
      assert(!is_nil_term(input));
      Term* header = input->list.head;
      assert(header->kind == TERM_LIST);
      output = make_procedure(arena, values, string("lambda"),  header, input->list.tail);
      break;
    } if (head->kind == TERM_ATOM && strings_equal(head->atom, string("define"))) {
      input = input->list.tail;
      
      assert(input->list.head != NULL && input->list.tail != NULL);
      Term* header = input->list.head;
      assert(header->kind == TERM_ATOM || header->kind == TERM_LIST);
      
      String name;
      Term*  value;
      if (header->kind == TERM_ATOM) {
	name  = header->atom;
	input = input->list.tail;
      
	assert(input->list.head != NULL && input->list.tail != NULL);
	value = evaluate_term(arena, values, input->list.head).term;
      } else {
	assert(header->list.head->kind == TERM_ATOM);
	name  = header->list.head->atom;
	value = make_procedure(arena, values, name, header->list.tail, input->list.tail);
      }
      Values* new = arena_allocate(arena, Values);
      new->name   = name;
      new->value  = value;
      new->next   = values;
      values      = new;
      output = value;
      if (output->kind == TERM_PROCEDURE) {
	output->procedure.captured = values;
      }
      break;
    }
    
    Term* operator = evaluate_term(arena, values, input->list.head).term;
    Term* operands = input->list.tail;
    assert(operator->kind == TERM_BUILT_IN || operator->kind == TERM_PROCEDURE);
    if (operator->kind == TERM_BUILT_IN) {
      output = built_ins[operator->built_in](arena, values, operands);
    } else if (operator->kind == TERM_PROCEDURE) {
      Procedure* procedure = &operator->procedure;
      Values*    scope     = values;
      Values*    last      = NULL;

      for (Values* i = procedure->captured; i != NULL; i = i->next) {
	Values* new = arena_allocate(arena, Values);
	*new        = *i;
	new->next   = scope;
	if (scope == values) {
	  scope = new;
	  last  = new;
	} else {
	  last->next = new;
	  last       = new;
	}
      }
      if (last != NULL) {
	last->next = values;
      }
      
      for (Term* i = procedure->parameters; i->list.head && i->list.tail; i = i->list.tail) {
	assert(operands->kind == TERM_LIST);
	assert(operands->list.head && operands->list.tail);
	Values* new = arena_allocate(arena, Values);
	new->name   = i->list.head->atom;
	new->value  = evaluate_term(arena, values, operands->list.head).term;
	new->next   = scope;
	scope       = new;
	operands    = operands->list.tail;
      }
      assert(is_nil_term(operands));

      output = &term_nil;
      for (Term* body = procedure->body; !is_nil_term(body); body = body->list.tail) {
	assert(body->kind == TERM_LIST);
	EvaluateResult result = evaluate_term(arena, scope, body->list.head);
	output                = result.term;
	scope                 = result.values;
      }
    }
    break;
  }

  EvaluateResult result;
  result.term   = output;
  result.values = values;
  return result;
}

int main(int argc, char** argv) {
  atexit(flush);
  srand(time(NULL));

  if (argc != 2) {
    print(string("Expected exactly one argument.\nUsage: vlisp program.vl\n"));
    exit(EXIT_FAILURE);
  }
  
  Arena arena;
  arena_initialize(&arena, 1ull << 32);

  String input = read_file(argv[1]);
  input        = clear_blanks(input);

  Values* values = NULL;
  for (U64 i = 0; i < length(built_ins); i++) {
    Term* term     = arena_allocate(&arena, Term);
    term->kind     = TERM_BUILT_IN;
    term->built_in = i;
    
    Values* new = arena_allocate(&arena, Values);
    new->name   = built_in_names[i];
    new->value  = term;
    new->next   = values;
    values      = new;
  }

  while (input.size > 0) {
    ParseResult parsed = parse(&arena, input);
    input              = parsed.rest;
    print(string("> "));
    print_term(parsed.term);
    print_char('\n');

    EvaluateResult result = evaluate_term(&arena, values, parsed.term);
    values                = result.values;
    print_term(result.term);
    print_char('\n');

    input = clear_blanks(input);
  }
}
