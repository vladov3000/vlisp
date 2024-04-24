typedef Term* (*BuiltInFn)(Arena* arena, Values* values, Term* operands);

static Term* built_in_add(Arena* arena, Values* values, Term* operands) {
  B32 promoted = false;
  I64 sum      = 0;
  F64 fsum     = 0;
  for (Term* i = operands; i->list.head != NULL && i->list.tail != NULL; i = i->list.tail) {
    Term* operand = evaluate_term(arena, values, i->list.head).term;
    assert(operand->kind == TERM_INTEGER || operand->kind == TERM_NUMBER);
    if (promoted) {
      fsum += operand->kind == TERM_INTEGER ? operand->integer : operand->number;
    } else {
      if (operand->kind == TERM_NUMBER) {
	promoted = true;
	fsum     = sum + operand->number;
      } else {
	sum += operand->integer;
      }
    }
  }

  Term* result = arena_allocate(arena, Term);
  if (promoted) {
    result->kind   = TERM_NUMBER;
    result->number = fsum;
  } else {
    result->kind    = TERM_INTEGER;
    result->integer = sum;
  }
  return result;
}

static Term* built_in_subtract(Arena* arena, Values* values, Term* operands) {
  if (is_nil_term(operands->list.tail)) {
    Term* result = evaluate_term(arena, values, operands->list.head).term;
    assert(result->kind == TERM_INTEGER || result->kind == TERM_NUMBER);
    if (result->kind == TERM_INTEGER) {
      result->integer *= -1;
    } else if (result->kind == TERM_NUMBER) {
      result->number *= -1;
    }
    return result;
  }
  
  B32 promoted = false;
  I64 sum      = 0;
  F64 fsum     = 0;
  for (Term* i = operands; i->list.head != NULL && i->list.tail != NULL; i = i->list.tail) {
    Term* operand = evaluate_term(arena, values, i->list.head).term;
    assert(operand->kind == TERM_INTEGER || operand->kind == TERM_NUMBER);
    if (i == operands) {
      if (operand->kind == TERM_INTEGER) {
	sum = operand->integer;
      } else {
	promoted = true;
	fsum     = operand->number;
      }
    } else {
      if (promoted) {
	fsum -= operand->kind == TERM_INTEGER ? operand->integer : operand->number;
      } else {
	if (operand->kind == TERM_NUMBER) {
	  promoted = true;
	  fsum     = sum - operand->number;
	} else {
	  sum -= operand->integer;
	}
      }
    }
  }

  Term* result = arena_allocate(arena, Term);
  if (promoted) {
    result->kind   = TERM_NUMBER;
    result->number = fsum;
  } else {
    result->kind    = TERM_INTEGER;
    result->integer = sum;
  }
  return result;
}

static Term* built_in_multiply(Arena* arena, Values* values, Term* operands) {
  B32 promoted = false;
  I64 product  = 1;
  F64 fproduct = 1;
  for (Term* i = operands; i->list.head != NULL && i->list.tail != NULL; i = i->list.tail) {
    Term* operand = evaluate_term(arena, values, i->list.head).term;
    assert(operand->kind == TERM_INTEGER || operand->kind == TERM_NUMBER);
    if (promoted) {
      fproduct *= operand->kind == TERM_INTEGER ? operand->integer : operand->number;
    } else {
      if (operand->kind == TERM_NUMBER) {
	promoted = true;
	fproduct = product * operand->number;
      } else {
	product *= operand->integer;
      }
    }
  }

  Term* result = arena_allocate(arena, Term);
  if (promoted) {
    result->kind   = TERM_NUMBER;
    result->number = fproduct;
  } else {
    result->kind    = TERM_INTEGER;
    result->integer = product;
  }
  return result;
}

static Term* built_in_divide(Arena* arena, Values* values, Term* operands) {
  B32 promoted = false;
  I64 product  = 1;
  F64 fproduct = 1;
  for (Term* i = operands; i->list.head != NULL && i->list.tail != NULL; i = i->list.tail) {
    Term* operand = evaluate_term(arena, values, i->list.head).term;
    assert(operand->kind == TERM_INTEGER || operand->kind == TERM_NUMBER);
    if (i == operands) {
      if (operand->kind == TERM_INTEGER) {
	product = operand->integer;
      } else {
	fproduct = operand->number;
	promoted = true;
      }
    } else {
      if (promoted) {
	fproduct /= operand->kind == TERM_INTEGER ? operand->integer : operand->number;
      } else {
	if (operand->kind == TERM_NUMBER) {
	  promoted = true;
	  fproduct = product / operand->number;
	} else {
	  product /= operand->integer;
	}
      }
    }
  }

  Term* result = arena_allocate(arena, Term);
  if (promoted) {
    result->kind   = TERM_NUMBER;
    result->number = fproduct;
  } else {
    result->kind    = TERM_INTEGER;
    result->integer = product;
  }
  return result;
}

static Term* built_in_less_than(Arena* arena, Values* values, Term* operands) {
  assert(operands->kind            == TERM_LIST);
  assert(operands->list.tail->kind == TERM_LIST);
  Term* left  = evaluate_term(arena, values, operands->list.head).term;
  Term* right = evaluate_term(arena, values, operands->list.tail->list.head).term;
  assert(left->kind  == TERM_INTEGER || left->kind  == TERM_NUMBER);
  assert(right->kind == TERM_INTEGER || right->kind == TERM_NUMBER);

  B32 truth;
  if (left->kind == TERM_INTEGER) {
    truth = right->kind == TERM_INTEGER
      ? left->integer < right->integer
      : left->integer < right->number;
  } else {
    truth = right->kind == TERM_INTEGER
      ? left->number < right->integer
      : left->number < right->number;
  }
  
  return truth ? &term_t : &term_nil;
}

static Term* built_in_equal(Arena* arena, Values* values, Term* operands) {
  assert(operands->kind            == TERM_LIST);
  assert(operands->list.tail->kind == TERM_LIST);
  Term* left  = evaluate_term(arena, values, operands->list.head).term;
  Term* right = evaluate_term(arena, values, operands->list.tail->list.head).term;
  assert(left->kind  == TERM_INTEGER || left->kind  == TERM_NUMBER || left->kind == TERM_ATOM);
  assert(right->kind == TERM_INTEGER || right->kind == TERM_NUMBER || right->kind == TERM_ATOM);

  B32 truth;
  if (left->kind == TERM_INTEGER) {
    truth = right->kind == TERM_INTEGER
      ? left->integer == right->integer
      : left->integer == right->number;
  } else if (left->kind == TERM_NUMBER) {
    truth = right->kind == TERM_INTEGER
      ? left->number == right->integer
      : left->number == right->number;
  } else {
    truth = right->kind == TERM_ATOM && strings_equal(left->atom, right->atom);
  }
  
  return truth ? &term_t : &term_nil;  
}

static Term* built_in_greater_than(Arena* arena, Values* values, Term* operands) {
  assert(operands->kind            == TERM_LIST);
  assert(operands->list.tail->kind == TERM_LIST);
  Term* left  = evaluate_term(arena, values, operands->list.head).term;
  Term* right = evaluate_term(arena, values, operands->list.tail->list.head).term;
  assert(left->kind  == TERM_INTEGER || left->kind  == TERM_NUMBER);
  assert(right->kind == TERM_INTEGER || right->kind == TERM_NUMBER);

  B32 truth;
  if (left->kind == TERM_INTEGER) {
    truth = right->kind == TERM_INTEGER
      ? left->integer > right->integer
      : left->integer > right->number;
  } else {
    truth = right->kind == TERM_INTEGER
      ? left->number > right->integer
      : left->number > right->number;
  }
  
  return truth ? &term_t : &term_nil;
}

static Term* built_in_cond(Arena* arena, Values* values, Term* operands) {
  for (Term* i = operands; i->list.head != NULL && i->list.tail != NULL; i = i->list.tail) {
    assert(i->kind == TERM_LIST);
    Term* entry = i->list.head;
    assert(entry->kind == TERM_LIST);
    Term* condition = evaluate_term(arena, values, entry->list.head).term;
    if (condition->kind == TERM_LIST && !condition->list.head && !condition->list.tail) {
      continue;
    } else {
      assert(entry->list.tail->kind == TERM_LIST);
      Term* value = evaluate_term(arena, values, entry->list.tail->list.head).term;
      return value;
    }
  }
  return &term_nil;
}

static Term* built_in_if(Arena* arena, Values* values, Term* operands) {
  assert(operands->kind == TERM_LIST);
  assert(operands->list.tail->kind == TERM_LIST);
  Term* condition = evaluate_term(arena, values, operands->list.head).term;
  if (is_nil_term(condition)) {
    Term* rest = operands->list.tail->list.tail;
    if (is_nil_term(rest)) {
      return &term_nil;
    } else {
      return evaluate_term(arena, values, rest->list.head).term;
    }
  } else {
    return evaluate_term(arena, values, operands->list.tail->list.head).term;
  }
}

static Term* built_in_and(Arena* arena, Values* values, Term* operands) {
  Term* value;
  for (Term* i = operands; i->list.head != NULL && i->list.tail != NULL; i = i->list.tail) {
    assert(i->kind == TERM_LIST);
    Term* entry = i->list.head;
    value       = evaluate_term(arena, values, i->list.head).term;
    if (is_nil_term(value)) {
      return &term_nil;
    }
  }
  return value;
}

static Term* built_in_or(Arena* arena, Values* values, Term* operands) {
  for (Term* i = operands; i->list.head != NULL && i->list.tail != NULL; i = i->list.tail) {
    assert(i->kind == TERM_LIST);
    Term* entry = i->list.head;
    Term* value = evaluate_term(arena, values, i->list.head).term;
    if (!is_nil_term(value)) {
      return value;
    }
  }
  return &term_nil;
}

static Term* built_in_not(Arena* arena, Values* values, Term* operands) {
  assert(operands->kind == TERM_LIST);
  assert(!is_nil_term(operands));
  Term* operand = evaluate_term(arena, values, operands->list.head).term;
  if (is_nil_term(operand)) {
    return &term_t;
  } else {
    return &term_nil;
  }
}

static Term* built_in_random(Arena* arena, Values* values, Term* operands) {
  assert(operands->kind == TERM_LIST);
  assert(!is_nil_term(operands));
  Term* operand = evaluate_term(arena, values, operands->list.head).term;
  assert(operand->kind == TERM_INTEGER || operand->kind == TERM_NUMBER);
  Term* result = arena_allocate(arena, Term);
  result->kind = operand->kind;
  if (operand->kind == TERM_INTEGER) {
    result->integer = rand() % operand->integer;
  } else {
    result->number = fmod(rand(), operand->number);
  }
  return result;
}

static Term* built_in_runtime(Arena* arena, Values* values, Term* operands) {
  Term* result    = arena_allocate(arena, Term);
  result->kind    = TERM_INTEGER;
  result->integer = clock() * 1000000 / CLOCKS_PER_SEC;
  return result;
}

static Term* built_in_display(Arena* arena, Values* values, Term* operands) {
  Term* result = &term_nil;
  for (Term* i = operands; !is_nil_term(i); i = i->list.tail) {
    assert(i->kind == TERM_LIST);
    result = evaluate_term(arena, values, i->list.head).term;
    if (result->kind == TERM_STRING) {
      print(result->string);
    } else {
      print_term(result);
    }
  }
  return result;
}

static Term* built_in_remainder(Arena* arena, Values* values, Term* operands) {
  assert(operands->list.tail->kind == TERM_LIST && !is_nil_term(operands->list.tail));
  Term* a = evaluate_term(arena, values, operands->list.head).term;
  Term* b = evaluate_term(arena, values, operands->list.tail->list.head).term;
  
  assert(a->kind == TERM_INTEGER || a->kind == TERM_NUMBER);
  assert(b->kind == TERM_INTEGER || b->kind == TERM_NUMBER);

  Term* result = arena_allocate(arena, Term);
  if (a->kind == TERM_INTEGER && b->kind == TERM_INTEGER) {
    result->kind    = TERM_INTEGER;
    result->integer = a->integer % b->integer;
  } else {
    result->kind   = TERM_NUMBER;
    F64 a_number   = a->kind == TERM_INTEGER ? a->integer : a->number;
    F64 b_number   = b->kind == TERM_INTEGER ? b->integer : b->number;
    result->number = fmod(a_number, b_number);
  }
  return result;
}

static Term* built_in_sin(Arena* arena, Values* values, Term* operands) {
  assert(operands->kind == TERM_LIST);
  assert(!is_nil_term(operands));
  Term* operand = evaluate_term(arena, values, operands->list.head).term;
  assert(operand->kind == TERM_INTEGER || operand->kind == TERM_NUMBER);
  Term* result   = arena_allocate(arena, Term);
  result->kind   = TERM_NUMBER;
  result->number = sin(operand->kind == TERM_INTEGER ? operand->integer : operand->number);
  return result;
}

static Term* built_in_cos(Arena* arena, Values* values, Term* operands) {
  assert(operands->kind == TERM_LIST);
  assert(!is_nil_term(operands));
  Term* operand = evaluate_term(arena, values, operands->list.head).term;
  assert(operand->kind == TERM_INTEGER || operand->kind == TERM_NUMBER);
  Term* result   = arena_allocate(arena, Term);
  result->kind   = TERM_NUMBER;
  result->number = cos(operand->kind == TERM_INTEGER ? operand->integer : operand->number);
  return result;
}

static Term* built_in_log(Arena* arena, Values* values, Term* operands) {
  assert(operands->kind == TERM_LIST);
  assert(!is_nil_term(operands));
  Term* operand = evaluate_term(arena, values, operands->list.head).term;
  assert(operand->kind == TERM_INTEGER || operand->kind == TERM_NUMBER);
  Term* result   = arena_allocate(arena, Term);
  result->kind   = TERM_NUMBER;
  result->number = log(operand->kind == TERM_INTEGER ? operand->integer : operand->number);
  return result;
}

static String built_in_names[] = {
  string("+"),
  string("-"),
  string("*"),
  string("/"),
  string("<"),
  string("="),
  string(">"),
  string("cond"),
  string("if"),
  string("and"),
  string("or"),
  string("not"),
  string("random"),
  string("runtime"),
  string("display"),
  string("remainder"),
  string("sin"),
  string("cos"),
  string("log"),
};

static BuiltInFn built_ins[] = {
  built_in_add,
  built_in_subtract,
  built_in_multiply,
  built_in_divide,
  built_in_less_than,
  built_in_equal,
  built_in_greater_than,
  built_in_cond,
  built_in_if,
  built_in_and,
  built_in_or,
  built_in_not,
  built_in_random,
  built_in_runtime,
  built_in_display,
  built_in_remainder,
  built_in_sin,
  built_in_cos,
  built_in_log,
};

