#ifndef clox_chunk_h
#define clox_chunk_h

#include "common.h"
#include "value.h"

typedef enum {
  OP_RETURN,
  OP_CONSTANT,
  OP_NEGATE,
  OP_ADD,
  OP_SUBTRACT,
  OP_MULTIPLY,
  OP_DIVIDE,
  OP_TRUE,
  OP_FALSE,
  OP_NIL,
  OP_NOT,
  OP_EQUAL,
  OP_GREATER,
  OP_LESS,
  OP_PRINT,
  OP_INDEX_GLOBAL,
  OP_INDEX_LOCAL,
  OP_POP,
  OP_POPN,
  OP_DEFINE_GLOBAL_CONST,
  OP_DEFINE_GLOBAL_VAR,
  OP_GET_GLOBAL,
  OP_SET_GLOBAL,
  OP_GET_PROPERTY,
  OP_SET_PROPERTY,
  OP_GET_LOCAL,
  OP_SET_LOCAL,
  OP_SET_ARRAY_LOCAL,
  OP_SET_ARRAY_GLOBAL,
  OP_JUMP_IF_FALSE,
  OP_JUMP_SWITCH,
  OP_SWITCH_END,
  OP_JUMP,
  OP_LOOP,
  OP_JUMP_DEFAULT,
  OP_CALL,
  OP_CLOSURE,
  OP_GET_UPVALUE,
  OP_SET_UPVALUE,
  OP_CLOSE_UPVALUE,
  OP_CLASS,
} OpCode;

typedef struct {
  int count;
  int capacity;
  uint8_t *code;
  int *lines;
  ValueArray constants;
} Chunk;

void initChunk(Chunk *chunk);
void freeChunk(Chunk *chunk);
void writeChunk(Chunk *chunk, uint8_t byte, int line);
int addConstant(Chunk *chunk, Value value);

#endif
