#include "vm.h"
#include "chunk.h"
#include "common.h"
#include "compiler.h"
#include "debug.h"
#include "memory.h"
#include "object.h"
#include "table.h"
#include "value.h"
#include <math.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef enum {
  FOUND,
  NOT_FOUND,
} IsFound;

IsFound isFound = NOT_FOUND;
VM vm;
static void runtimeError(const char *format, ...);

static Value clockNative(int argCount, Value *args) {
  return NUMBER_VAL((double)clock() / CLOCKS_PER_SEC);
}

static Value randomNative(int argCount, Value *args) {
  if (argCount != 0) {
    runtimeError("'range' function takes 0 arguments");
  }

  return NUMBER_VAL((double)rand());
}

static Value rangeNative(int argCount, Value *args) {
  if (argCount != 1) {
    runtimeError("'range' function takes 1 arguments");
  }

  int arg1 = AS_NUMBER(*args);
  return NUMBER_VAL((double)(rand() % arg1));
}

static Value sqrtNative(int argCount, Value *args) {
  if (argCount != 1) {
    runtimeError("'range' function takes 1 argument");
  }

  double arg1 = AS_NUMBER(*args);
  double result = 1.0;
  for (int i = 1; i <= 10; i++) {
    result -= (result * result - arg1) / (2 * result);
  }

  return NUMBER_VAL(result);
}

static Value fgetsNative(int argCount, Value *args) {
  char input[1024];
  fgets(input, sizeof(input), stdin);
  int i = 0;
  while (input[i] != '\0') {
    i++;
  }

  return OBJ_VAL(copyString(input, i - 1));
}

static Value arrSize(int argCount, Value *args) {
  if (argCount != 1) {
    runtimeError("'arrSize' function takes 1 argument");
  }
  if (!isObjType(*args, OBJ_ARRAY)) {
    runtimeError("'arrSize' takes only array object");
  }

  return NUMBER_VAL(AS_ARRAY(*args)->array.count);
}

static void resetStack() {
  vm.stackTop = vm.stack;
  vm.frameCount = 0;
  vm.objects = NULL;
  vm.bytesAllocated = 0;
  vm.nextGC = 1024 * 1024;
  vm.grayCount = 0;
  vm.grayCapacity = 0;
  vm.grayStack = NULL;
  vm.openUpvalues = NULL;
  initTable(&vm.strings);
  initTable(&vm.globals);
}

static void runtimeError(const char *format, ...) {
  va_list args;
  va_start(args, format);
  vfprintf(stderr, format, args);
  va_end(args);
  fputs("\n", stderr);

  CallFrame *frame = &vm.frames[vm.frameCount - 1];
  size_t instruction = frame->ip - frame->function->chunk.code - 1;
  int line = frame->function->chunk.lines[instruction];
  fprintf(stderr, "[line %d] in script\n", line);

  for (int i = vm.frameCount - 1; i >= 0; i--) {
    CallFrame *frame = &vm.frames[i];
    ObjFunction *function = frame->closure->function;
    size_t instruction = frame->ip - function->chunk.code - 1;
    fprintf(stderr, "[line %d] in ", function->chunk.lines[instruction]);
    if (function->name == NULL) {
      fprintf(stderr, "script\n");
    } else {
      fprintf(stderr, "%s()\n", function->name->chars);
    }
  }
  resetStack();
}

static void defineNative(const char *name, NativeFn function) {
  push(OBJ_VAL(copyString(name, (int)strlen(name))));
  push(OBJ_VAL(newNative(function)));
  tableSet(&vm.globals, AS_STRING(vm.stack[0]), vm.stack[1]);
  pop();
  pop();
}

void initVM() {
  resetStack();

  defineNative("clock", clockNative);
  defineNative("random", randomNative);
  defineNative("range", rangeNative);
  defineNative("fgets", fgetsNative);
  defineNative("sqrt", sqrtNative);
  defineNative("arrSize", arrSize);
}

void freeVM() {
  freeTable(&vm.strings);
  freeTable(&vm.globals);
  freeObjects();
}

static Value peek(int distance) { return vm.stackTop[-1 - distance]; }

static bool call(ObjClosure *closure, int argCount) {
  if (argCount != closure->function->arity) {
    runtimeError("Expected %d arguments but got %d.", closure->function->arity,
                 argCount);
  }

  if (vm.frameCount == FRAMES_MAX) {
    runtimeError("Stack overflow.");
    return false;
  }

  CallFrame *frame = &vm.frames[vm.frameCount++];
  frame->closure = closure;
  frame->ip = closure->function->chunk.code;
  frame->slots = vm.stackTop - argCount - 1;
  return true;
}

static bool callValue(Value callee, int argCount) {
  if (IS_OBJ(callee)) {
    switch (OBJ_TYPE(callee)) {
    case OBJ_NATIVE: {
      NativeFn native = AS_NATIVE(callee);
      Value result = native(argCount, vm.stackTop - argCount);
      vm.stackTop -= argCount + 1;
      push(result);
      return true;
    }
    case OBJ_CLOSURE:
      return call(AS_CLOSURE(callee), argCount);
    default:
      break; // Non-callable object type.
    }
  }
  runtimeError("Can only call functions and classes.");
  return false;
}

static ObjUpvalue *captureUpvalue(Value *local) {
  ObjUpvalue *prevUpvalue = NULL;
  ObjUpvalue *upvalue = vm.openUpvalues;
  while (upvalue != NULL && upvalue->location > local) {
    prevUpvalue = upvalue;
    upvalue = upvalue->next;
  }
  if (upvalue != NULL && upvalue->location == local) {
    return upvalue;
  }
  ObjUpvalue *createdUpvalue = newUpvalue(local);
  if (prevUpvalue == NULL) {
    vm.openUpvalues = createdUpvalue;
  } else {
    prevUpvalue->next = createdUpvalue;
  }
  return createdUpvalue;
}

static void closeUpvalues(Value *last) {
  while (vm.openUpvalues != NULL && vm.openUpvalues->location >= last) {
    ObjUpvalue *upvalue = vm.openUpvalues;
    upvalue->closed = *upvalue->location;
    upvalue->location = &upvalue->closed;
    vm.openUpvalues = upvalue->next;
  }
}

void push(Value value) {
  *vm.stackTop = value;
  vm.stackTop++;
}

bool isFalsey(Value value) {
  return IS_NIL(value) || (IS_BOOL(value) && !AS_BOOL(value));
}

static void concatenate() {
  ObjString *b = AS_STRING(peek(0));
  ObjString *a = AS_STRING(peek(1));

  int length = a->length + b->length;
  char *chars = ALLOCATE(char, length + 1);
  memcpy(chars, a->chars, a->length);
  memcpy(chars + a->length, b->chars, b->length);
  chars[length] = '\0';

  ObjString *result = takeString(chars, length);
  pop();
  pop();
  push(OBJ_VAL(result));
}

Value pop() {
  vm.stackTop--;
  return *vm.stackTop;
}

static InterpretResult run() {
  CallFrame *frame = &vm.frames[vm.frameCount - 1];

#define READ_BYTE() (*frame->ip++)

#define READ_SHORT()                                                           \
  (frame->ip += 2, (uint16_t)((frame->ip[-2] << 8) | frame->ip[-1]))

#define READ_CONSTANT()                                                        \
  (frame->closure->function->chunk.constants.values[READ_BYTE()])

#define READ_STRING() AS_STRING(READ_CONSTANT())

#define BINARY_OP(valueType, op)                                               \
  do {                                                                         \
    if (!IS_NUMBER(peek(0)) || !IS_NUMBER(peek(1))) {                          \
      runtimeError("Operands must be numbers.");                               \
      return INTERPRET_RUNTIME_ERROR;                                          \
    }                                                                          \
    double b = AS_NUMBER(pop());                                               \
    double a = AS_NUMBER(pop());                                               \
    push(valueType(a op b));                                                   \
  } while (false)

  for (;;) {
#ifdef DEBUG_TRACE_EXECUTION

    printf("          ");
    for (Value *slot = vm.stack; slot < vm.stackTop; slot++) {
      printf("[ ");
      printValue(*slot);
      printf(" ]");
    }
    printf("\n");

#endif

    uint8_t instruction;
    switch (instruction = READ_BYTE()) {
    case OP_CONSTANT: {
      Value constant = READ_CONSTANT();
      push(constant);
      break;
    }
    case OP_RETURN: {
      Value result = pop();
      closeUpvalues(frame->slots);
      vm.frameCount--;
      if (vm.frameCount == 0) {
        pop();
        return INTERPRET_OK;
      }

      vm.stackTop = frame->slots;
      push(result);
      frame = &vm.frames[vm.frameCount - 1];
      break;
    }
    case OP_NEGATE:
      if (!IS_NUMBER(peek(0))) {
        runtimeError("Operand must be a number.");
        return INTERPRET_RUNTIME_ERROR;
      }
      push(NUMBER_VAL(-AS_NUMBER(pop())));
      break;
    case OP_ADD: {
      if (IS_STRING(peek(0)) && IS_STRING(peek(1))) {
        concatenate();
      } else if (IS_NUMBER(peek(0)) && IS_NUMBER(peek(1))) {
        double b = AS_NUMBER(pop());
        double a = AS_NUMBER(pop());
        push(NUMBER_VAL(a + b));
      } else {
        runtimeError("Operands must be two numbers or two strings.");
        return INTERPRET_RUNTIME_ERROR;
      }
      break;
    }
    case OP_SUBTRACT:
      BINARY_OP(NUMBER_VAL, -);
      break;
    case OP_MULTIPLY:
      BINARY_OP(NUMBER_VAL, *);
      break;
    case OP_DIVIDE:
      BINARY_OP(NUMBER_VAL, /);
      break;
    case OP_NIL:
      push(NIL_VAL);
      break;
    case OP_TRUE:
      push(BOOL_VAL(true));
      break;
    case OP_FALSE:
      push(BOOL_VAL(false));
      break;
    case OP_NOT:
      push(BOOL_VAL(isFalsey(pop())));
      break;
    case OP_EQUAL: {
      Value b = pop();
      Value a = pop();
      push(BOOL_VAL(valuesEqual(a, b)));
      break;
    }
    case OP_GREATER:
      BINARY_OP(BOOL_VAL, >);
      break;
    case OP_LESS:
      BINARY_OP(BOOL_VAL, <);
      break;
    case OP_PRINT: {
      printValue(pop());
      printf("\n");
      break;
    }
    case OP_POP:
      pop();
      break;
    case OP_POPN: {
      Value times = READ_CONSTANT();
      for (int i = 0; i < times.as.number; i++) {
        pop();
      }
      break;
    }
    case OP_DEFINE_GLOBAL_VAR: {
      ObjString *name = READ_STRING();
      tableSetVariable(&vm.globals, name, peek(0), VAR, 0);
      pop();
      break;
    }
    case OP_DEFINE_GLOBAL_CONST: {
      ObjString *name = READ_STRING();
      tableSetVariable(&vm.globals, name, peek(0), CONST, 0);
      pop();
      break;
    }
    case OP_GET_GLOBAL: {
      ObjString *name = READ_STRING();
      Value value;
      if (!tableGet(&vm.globals, name, &value)) {
        runtimeError("Undefined variable '%s'.", name->chars);
        return INTERPRET_RUNTIME_ERROR;
      }
      push(value);
      break;
    }
    case OP_SET_GLOBAL: {
      ObjString *name = READ_STRING();
      Kind err = tableSetVariable(&vm.globals, name, peek(0), NONE, 1);
      if (err == UNASSINGABLE) {
        tableDelete(&vm.globals, name);
        runtimeError("Cannot mutate constant variable '%s'.", name->chars);
        return INTERPRET_RUNTIME_ERROR;
      } else if (err == UNDEFINED) {
        tableDelete(&vm.globals, name);
        runtimeError("Undefined variable '%s'.", name->chars);
        return INTERPRET_RUNTIME_ERROR;
      } else {
        break;
      }
    }
    case OP_GET_LOCAL: {
      uint8_t slot = READ_BYTE();
      push(frame->slots[slot]);
      break;
    }
    case OP_SET_LOCAL: {
      uint8_t slot = READ_BYTE();
      frame->slots[slot] = peek(0);
      break;
    }
    case OP_SET_ARRAY_LOCAL: {
      uint8_t slot = READ_BYTE();
      Value value = pop();
      int offest = AS_NUMBER(peek(0));
      ValueArray *array = &AS_ARRAY(frame->slots[slot])->array;
      if (array->count < offest)
        runtimeError("index array is bigger than array size");
      if (offest == array->count)
        writeValueArray(array, value);
      else
        array->values[offest] = value;

      break;
    }
    case OP_SET_ARRAY_GLOBAL: {
      ObjString *name = READ_STRING();
      Value val = pop();
      int offest = AS_NUMBER(peek(0));
      printf("index: %d\n", offest);
      printValue(val);
      printf("\n");
      printf("%s\n", name->chars);
      Value value;
      tableGet(&vm.globals, name, &value);
      ValueArray *array = &AS_ARRAY(value)->array;
      if (array->count < offest)
        runtimeError("index array is bigger than array size");
      if (offest == array->count)
        writeValueArray(array, val);
      else
        array->values[offest] = val;

      printf("%d\n", AS_ARRAY(value)->array.count);
      Kind err = tableSetVariable(&vm.globals, name, value, NONE, 1);
      if (err == UNASSINGABLE) {
        tableDelete(&vm.globals, name);
        runtimeError("Cannot mutate constant variable '%s'.", name->chars);
        return INTERPRET_RUNTIME_ERROR;
      } else if (err == UNDEFINED) {
        tableDelete(&vm.globals, name);
        runtimeError("Undefined variable '%s'.", name->chars);
        return INTERPRET_RUNTIME_ERROR;
      } else {
        break;
      }
      break;
    }
    case OP_JUMP: {
      uint16_t offest = READ_SHORT();
      frame->ip += offest;
      break;
    }
    case OP_JUMP_IF_FALSE: {
      uint16_t offest = READ_SHORT();
      if (isFalsey(peek(0))) {
        frame->ip += offest;
      }
      break;
    }
    case OP_JUMP_SWITCH: {
      uint16_t offest = READ_SHORT();
      Value b = pop();
      Value a = peek(0);

      if (!valuesEqual(a, b)) {
        frame->ip += offest;
      } else {
        isFound = FOUND;
      }
      break;
    }
    case OP_JUMP_DEFAULT: {
      uint16_t offest = READ_SHORT();

      if (isFound == FOUND) {
        frame->ip += offest;
        isFound = NOT_FOUND;
      }

      break;
    }
    case OP_LOOP: {
      uint16_t offest = READ_SHORT();
      frame->ip -= offest;
      break;
    }
    case OP_CALL: {
      int argCount = READ_BYTE();
      if (!callValue(peek(argCount), argCount)) {
        return INTERPRET_RUNTIME_ERROR;
      }
      frame = &vm.frames[vm.frameCount - 1];
      break;
    }
    case OP_CLOSURE: {
      ObjFunction *function = AS_FUNCTION(READ_CONSTANT());
      ObjClosure *closure = newClosure(function);
      push(OBJ_VAL(closure));
      for (int i = 0; i < closure->upvalueCount; i++) {
        uint8_t isLocal = READ_BYTE();
        uint8_t index = READ_BYTE();
        if (isLocal) {
          closure->upvalues[i] = captureUpvalue(frame->slots + index);
        } else {
          closure->upvalues[i] = frame->closure->upvalues[index];
        }
      }
      break;
    }
    case OP_GET_UPVALUE: {
      uint8_t slot = READ_BYTE();
      push(*frame->closure->upvalues[slot]->location);
      break;
    }
    case OP_SET_UPVALUE: {
      uint8_t slot = READ_BYTE();
      Value value = peek(0);
      if (IS_ARRAY(*frame->closure->upvalues[slot]->location)) {
        int index = AS_NUMBER(peek(1));
        printValue(AS_ARRAY(*frame->closure->upvalues[slot]->location)
                       ->array.values[index - 1]);
        printf("dsdsds\n");
        printf("%d\n", index);
        AS_ARRAY(*frame->closure->upvalues[slot]->location)
            ->array.values[index - 1] = value;
        pop();
      } else {
        *frame->closure->upvalues[slot]->location = value;
      }
      break;
    }
    case OP_CLOSE_UPVALUE:
      closeUpvalues(vm.stackTop - 1);
      pop();
      break;
    case OP_INDEX_LOCAL: {
      uint8_t slot = READ_BYTE();
      int index = AS_NUMBER(pop());
      ObjArray *array = AS_ARRAY(frame->slots[slot]);
      if (index >= array->array.count) {
        runtimeError("Index is bigger than array size");
        return INTERPRET_RUNTIME_ERROR;
      }
      push(AS_ARRAY(frame->slots[slot])->array.values[index]);
      break;
    }
    case OP_INDEX_GLOBAL: {
      uint8_t index = AS_NUMBER(pop());
      ObjString *name = READ_STRING();
      Value value;
      if (!tableGet(&vm.globals, name, &value)) {
        runtimeError("Undefined variable '%s'.", name->chars);
        return INTERPRET_RUNTIME_ERROR;
      }
      ValueArray arr = AS_ARRAY(value)->array;
      for (int i = 0; i < arr.count; i++) {
        printValue(arr.values[i]);
      }
      push(AS_ARRAY(value)->array.values[index]);
      break;
    }
    }
  }

#undef READ_CONSTANT
#undef READ_BYTE
#undef READ_SHORT
#undef BINARY_OP
#undef READ_STRING
}

InterpretResult interpret(const char *source) {
  ObjFunction *function = compile(source);
  if (function == NULL)
    return INTERPRET_COMPILE_ERROR;

  push(OBJ_VAL(function));
  ObjClosure *closure = newClosure(function);
  pop();
  push(OBJ_VAL(closure));
  call(closure, 0);

  return run();
}
