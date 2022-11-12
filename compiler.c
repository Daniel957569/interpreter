#include <stdio.h>

#include "chunk.h"
#include "common.h"
#include "compiler.h"
#include "object.h"
#include "scanner.h"
#include "value.h"
#include "vm.h"
#include <stdlib.h>
#include <string.h>

#ifdef DEBUG_PRINT_CODE
#include "debug.h"
#endif

static void BYTE_TO_BITS(int byte) {
  printf("yooo the byte: ");
  char byte1 = (byte & 0x80) ? printf("%c", '1') : printf("%c", '0');
  char byte3 = (byte & 0x40) ? printf("%c", '1') : printf("%c", '0');
  char byte4 = (byte & 0x20) ? printf("%c", '1') : printf("%c", '0');
  char byte5 = (byte & 0x10) ? printf("%c", '1') : printf("%c", '0');
  char byte6 = (byte & 0x08) ? printf("%c", '1') : printf("%c", '0');
  char byte7 = (byte & 0x06) ? printf("%c", '1') : printf("%c", '0');
  char byte8 = (byte & 0x04) ? printf("%c", '1') : printf("%c", '0');
  char byte9 = (byte & 0x02) ? printf("%c", '1') : printf("%c", '0');

  printf("\n");
}

typedef enum {
  PREC_NONE,
  PREC_ASSIGNMENT, // =
  PREC_OR,         // or
  PREC_AND,        // and
  PREC_EQUALITY,   // == !=
  PREC_COMPARISON, // < > <= >=
  PREC_TERM,       // + -
  PREC_FACTOR,     // * /
  PREC_UNARY,      // ! -
  PREC_CALL,       // . ()
  PREC_PRIMARY
} Precedence;

typedef void (*ParseFn)(bool canAssign);
typedef struct {
  ParseFn prefix;
  ParseFn infix;
  Precedence precedence;
} ParseRule;

typedef struct {
  Token name;
  int depth;
  Type type;
} Local;

typedef struct {
  int arg;
  Type type;
  Token *name;
} resolveTuple;

typedef enum {
  TYPE_FUNCTION,
  TYPE_SCRIPT,
} FunctionType;

typedef struct Compiler {
  struct Compiler *enclosing;
  ObjFunction *function;
  FunctionType type;
  Local locals[UINT8_COUNT];
  int localCount;
  int scopeDepth;
} Compiler;

typedef struct {
  Token current;
  Token previous;
  bool hadError;
  bool panicMode;
} Parser;

Parser parser;
Compiler *current = NULL;
Chunk *compilingChunk;
int hasBreak = 0;
int hasContinue = 0;

static Chunk *currentChunk() { return &current->function->chunk; }

static void errorAt(Token *token, const char *message) {
  if (parser.panicMode)
    return;
  parser.panicMode = true;
  fprintf(stderr, "[line %d] Error", token->line);

  if (token->type == TOKEN_EOF) {
    fprintf(stderr, " at end");
  } else if (token->type == TOKEN_ERROR) {
    // Nothing.
  } else {
    fprintf(stderr, " at '%.*s'", token->length, token->start);
  }

  fprintf(stderr, ": %s\n", message);
  parser.hadError = true;
}

static void error(const char *message) { errorAt(&parser.previous, message); }

static void errorAtCurrent(const char *message) {
  errorAt(&parser.current, message);
}

static void advance() {
  parser.previous = parser.current;

  for (;;) {
    parser.current = scanToken();
    if (parser.current.type != TOKEN_ERROR)
      break;

    errorAtCurrent(parser.current.start);
  }
}

static void consume(TokenType type, const char *message) {
  if (parser.current.type == type) {
    advance();
    return;
  }

  errorAtCurrent(message);
}

static bool check(TokenType type) { return parser.current.type == type; }

static bool match(TokenType type) {
  if (!check(type))
    return false;
  advance();
  return true;
}

static void emitByte(uint8_t byte) {
  writeChunk(currentChunk(), byte, parser.previous.line);
}

static void emitBytes(uint8_t byte1, uint8_t byte2) {
  emitByte(byte1);
  emitByte(byte2);
}

static void emitLoop(int loopStart) {
  emitByte(OP_LOOP);

  int offest = currentChunk()->count - loopStart + 2;
  if (offest > UINT16_MAX)
    error("Loop body too large");

  emitByte((offest >> 8) & 0xff);
  emitByte(offest & 0xff);
}

static int emitJump(uint8_t instruction) {
  emitByte(instruction);
  emitByte(0xff);
  emitByte(0xff);
  return currentChunk()->count - 2;
}

static void emitReturn() {
  emitByte(OP_NIL);
  emitByte(OP_RETURN);
}

static uint8_t makeConstant(Value value) {
  int constant = addConstant(currentChunk(), value);
  if (constant > UINT8_MAX) {
    error("Too many constants in one chunk.");
    return 0;
  }

  return (uint8_t)constant;
}

static void emitConstant(Value value) {
  emitBytes(OP_CONSTANT, makeConstant(value));
}

static void patchJump(int offest, int type) {
  // -2 adjust for the bytecode for the jump offest itself

  int jump = (type == 0) ? currentChunk()->count - offest - 2
                         : currentChunk()->count - offest + 2;

  printf("ddd%d\n", jump);
  if (jump > UINT16_MAX) {
    error("Too much code to jump over");
  }

  currentChunk()->code[offest] = (jump >> 8) & 0xff;
  currentChunk()->code[offest + 1] = jump & 0xff;
}

static void initCompiler(Compiler *compiler, FunctionType type) {
  compiler->enclosing = current;
  compiler->function = NULL;
  compiler->type = type;
  compiler->localCount = 0;
  compiler->scopeDepth = 0;
  compiler->function = newFunction();
  current = compiler;
  if (type != TYPE_SCRIPT) {
    current->function->name =
        copyString(parser.previous.start, parser.previous.length);
  }

  Local *local = &current->locals[current->localCount++];
  local->depth = 0;
  local->name.start = "";
  local->name.length = 0;
  local->type = NONE;
}

static ObjFunction *endCompiler() {
  emitReturn();
  ObjFunction *function = current->function;

#ifdef DEBUG_PRINT_CODE
  if (!parser.hadError) {
    disassembleChunk(currentChunk(), function->name != NULL
                                         ? function->name->chars
                                         : "<script>");
  }
#endif
  current = current->enclosing;
  return function;
}

static void beginScope() { current->scopeDepth++; }

static void endScope() {
  current->scopeDepth--;
  int times = 0;

  while (current->localCount > 0 &&
         current->locals[current->localCount - 1].depth > current->scopeDepth) {
    times++;
    current->localCount--;
  }
  emitBytes(OP_POPN, makeConstant(NUMBER_VAL(times)));
}

static void expression();
static void statement();
static void declaration();
static ParseRule *getRule(TokenType type);
static void parsePrecedence(Precedence precedence);
static void variableDeclaration(Type type);

static uint8_t identifierConstant(Token *name) {
  return makeConstant(OBJ_VAL(copyString(name->start, name->length)));
}

static bool identifiersEqual(Token *a, Token *b) {
  if (a->length != b->length)
    return false;
  return memcmp(a->start, b->start, a->length) == 0;
}

static resolveTuple createTuple(int arg, Type type, Token *name) {
  resolveTuple tuple;
  tuple.type = type;
  tuple.arg = arg;
  tuple.name = name;

  return tuple;
}

static resolveTuple resolveLocal(Compiler *compiler, Token *name) {
  for (int i = compiler->localCount - 1; i >= 0; i--) {
    Local *local = &compiler->locals[i];
    if (identifiersEqual(name, &local->name)) {
      return createTuple(i, local->type, &local->name);
    }

    /* if (local->depth == -1) { */
    /*   error("Can't read local variable in its own initializer."); */
    /* } */
  }

  return createTuple(-1, NONE, NULL);
}

static void addLocal(Token name, Type type) {
  if (current->localCount == UINT8_COUNT) {
    error("Too many local variables in function.");
    return;
  }

  Local *local = &current->locals[current->localCount++];
  local->name = name;
  local->depth = -1;
  local->type = type;
}

static void declareVariable(Type type) {
  if (current->scopeDepth == 0)
    return;

  Token *name = &parser.previous;
  for (int i = current->localCount - 1; i >= 0; i--) {
    Local *local = &current->locals[i];
    if (local->depth != -1 && local->depth < current->scopeDepth) {
      break;
    }

    if (identifiersEqual(name, &local->name)) {
      error("Already a variable with this name in this scope.");
    }
  }

  addLocal(*name, type);
}

static uint8_t parseVariable(const char *errorMessage, Type type) {
  consume(TOKEN_IDENTIFIER, errorMessage);

  declareVariable(type);
  if (current->scopeDepth > 0)
    return 0;

  return identifierConstant(&parser.previous);
}

static void markInitialized() {
  if (current->scopeDepth == 0)
    return;
  current->locals[current->localCount - 1].depth = current->scopeDepth;
}

static void defineVariable(uint8_t global, Type type) {
  if (current->scopeDepth > 0) {
    markInitialized();
    return;
  }
  OpCode varType =
      (type == VAR) ? OP_DEFINE_GLOBAL_VAR : OP_DEFINE_GLOBAL_CONST;

  emitBytes(varType, global);
}

static void and_(bool canAssign) {
  int endJump = emitJump(OP_JUMP_IF_FALSE);

  emitByte(OP_POP);
  parsePrecedence(PREC_AND);

  patchJump(endJump, 0);
}

static void binary(bool canAssign) {
  TokenType operatorType = parser.previous.type;
  ParseRule *rule = getRule(operatorType);
  parsePrecedence((Precedence)(rule->precedence + 1));

  switch (operatorType) {
  case TOKEN_BANG_EQUAL:
    emitBytes(OP_EQUAL, OP_NOT);
    break;
  case TOKEN_EQUAL_EQUAL:
    emitByte(OP_EQUAL);
    break;
  case TOKEN_GREATER:
    emitByte(OP_GREATER);
    break;
  case TOKEN_GREATER_EQUAL:
    emitBytes(OP_LESS, OP_NOT);
    break;
  case TOKEN_LESS:
    emitByte(OP_LESS);
    break;
  case TOKEN_LESS_EQUAL:
    emitBytes(OP_GREATER, OP_NOT);
    break;
  case TOKEN_PLUS:
    emitByte(OP_ADD);
    break;
  case TOKEN_MINUS:
    emitByte(OP_SUBTRACT);
    break;
  case TOKEN_STAR:
    emitByte(OP_MULTIPLY);
    break;
  case TOKEN_SLASH:
    emitByte(OP_DIVIDE);
    break;
  default:
    return; // Unreachable.
  }
}

static uint8_t argumentsList() {
  uint8_t argCount = 0;
  if (!check(TOKEN_RIGHT_PAREN)) {
    do {
      expression();
      if (argCount == 255) {
        error("Can't have more than 255 arguments.");
      }
      argCount++;
    } while (match(TOKEN_COMMA));
  }
  consume(TOKEN_RIGHT_PAREN, "Expect ')' after arguments");
  return argCount;
}

static void call(bool canAssign) {
  uint8_t argCount = argumentsList();
  emitBytes(OP_CALL, argCount);
}

static void literal(bool canAssign) {
  switch (parser.previous.type) {
  case TOKEN_FALSE:
    emitByte(OP_FALSE);
    break;
  case TOKEN_TRUE:
    emitByte(OP_TRUE);
    break;
  case TOKEN_NIL:
    emitByte(OP_NIL);
    break;
  default:
    // Unreachable
    return;
  }
}

static void grouping(bool canAssign) {
  expression();
  consume(TOKEN_RIGHT_PAREN, "Expect ')' after expression.");
}

static void number(bool canAssign) {
  double value = strtod(parser.previous.start, NULL);
  emitConstant(NUMBER_VAL(value));
}

static void or_(bool canAssign) {
  int elseJump = emitJump(OP_JUMP_IF_FALSE);
  int endJump = emitJump(OP_JUMP);

  patchJump(elseJump, 0);
  emitByte(OP_POP);

  parsePrecedence(PREC_OR);
  patchJump(endJump, 0);
}

static void string(bool canAssign) {
  emitConstant(OBJ_VAL(
      copyString(parser.previous.start + 1, parser.previous.length - 2)));
}

static void namedVariable(Token name, bool canAssign) {
  uint8_t getOp, setOp;
  resolveTuple tuple = resolveLocal(current, &name);
  if (tuple.arg != -1) {
    getOp = OP_GET_LOCAL;
    setOp = OP_SET_LOCAL;
  } else {
    tuple.arg = identifierConstant(&name);
    getOp = OP_GET_GLOBAL;
    setOp = OP_SET_GLOBAL;
  }

  if (match(TOKEN_PLUS) && match(TOKEN_PLUS)) {
    if (tuple.type == CONST) {
      errorAt(tuple.name, "Cannot mutate constant variable");
    }

    emitBytes(getOp, (uint8_t)tuple.arg);
    emitConstant(NUMBER_VAL(1));
    emitByte(OP_ADD);
    emitBytes(setOp, (uint8_t)tuple.arg);
  } else if (canAssign && match(TOKEN_EQUAL)) {
    if (tuple.type == CONST) {
      errorAt(tuple.name, "Cannot mutate constant variable");
    }
    expression();
    emitBytes(setOp, (uint8_t)tuple.arg);

  } else {
    emitBytes(getOp, (uint8_t)tuple.arg);
  }
}

static void variable(bool canAssign) {
  namedVariable(parser.previous, canAssign);
}

static void unary(bool canAssign) {
  TokenType operatorType = parser.previous.type;

  // Compile the operand.
  parsePrecedence(PREC_UNARY);

  // Emit the operator instruction.
  switch (operatorType) {
  case TOKEN_BANG:
    emitByte(OP_NOT);
    break;
  case TOKEN_MINUS:
    emitByte(OP_NEGATE);
    break;
  default:
    return; // Unreachable.
  }
}

ParseRule rules[] = {
    [TOKEN_LEFT_PAREN] = {grouping, call, PREC_CALL},
    [TOKEN_RIGHT_PAREN] = {NULL, NULL, PREC_NONE},
    [TOKEN_LEFT_BRACE] = {NULL, NULL, PREC_NONE},
    [TOKEN_RIGHT_BRACE] = {NULL, NULL, PREC_NONE},
    [TOKEN_COMMA] = {NULL, NULL, PREC_NONE},
    [TOKEN_DOT] = {NULL, NULL, PREC_NONE},
    [TOKEN_MINUS] = {unary, binary, PREC_TERM},
    [TOKEN_PLUS] = {NULL, binary, PREC_TERM},
    [TOKEN_SEMICOLON] = {NULL, NULL, PREC_NONE},
    [TOKEN_SLASH] = {NULL, binary, PREC_FACTOR},
    [TOKEN_STAR] = {NULL, binary, PREC_FACTOR},
    [TOKEN_BANG] = {unary, NULL, PREC_NONE},
    [TOKEN_BANG_EQUAL] = {NULL, binary, PREC_EQUALITY},
    [TOKEN_EQUAL] = {NULL, NULL, PREC_NONE},
    [TOKEN_EQUAL_EQUAL] = {NULL, binary, PREC_EQUALITY},
    [TOKEN_GREATER] = {NULL, binary, PREC_COMPARISON},
    [TOKEN_GREATER_EQUAL] = {NULL, binary, PREC_COMPARISON},
    [TOKEN_LESS] = {NULL, binary, PREC_COMPARISON},
    [TOKEN_LESS_EQUAL] = {NULL, binary, PREC_COMPARISON},
    [TOKEN_IDENTIFIER] = {variable, NULL, PREC_NONE},
    [TOKEN_STRING] = {string, NULL, PREC_NONE},
    [TOKEN_NUMBER] = {number, NULL, PREC_NONE},
    [TOKEN_AND] = {NULL, and_, PREC_AND},
    [TOKEN_CLASS] = {NULL, NULL, PREC_NONE},
    [TOKEN_ELSE] = {NULL, NULL, PREC_NONE},
    [TOKEN_FALSE] = {literal, NULL, PREC_NONE},
    [TOKEN_FOR] = {NULL, NULL, PREC_NONE},
    [TOKEN_FUN] = {NULL, NULL, PREC_NONE},
    [TOKEN_IF] = {NULL, NULL, PREC_NONE},
    [TOKEN_NIL] = {literal, NULL, PREC_NONE},
    [TOKEN_OR] = {NULL, or_, PREC_OR},
    [TOKEN_PRINT] = {NULL, NULL, PREC_NONE},
    [TOKEN_RETURN] = {NULL, NULL, PREC_NONE},
    [TOKEN_SUPER] = {NULL, NULL, PREC_NONE},
    [TOKEN_THIS] = {literal, NULL, PREC_NONE},
    [TOKEN_TRUE] = {NULL, NULL, PREC_NONE},
    [TOKEN_VAR] = {NULL, NULL, PREC_NONE},
    [TOKEN_WHILE] = {NULL, NULL, PREC_NONE},
    [TOKEN_ERROR] = {NULL, NULL, PREC_NONE},
    [TOKEN_EOF] = {NULL, NULL, PREC_NONE},
};

static void parsePrecedence(Precedence precedence) {
  advance();
  ParseFn prefixRule = getRule(parser.previous.type)->prefix;
  if (prefixRule == NULL) {
    error("Expect expression.");
    return;
  }

  bool canAssign = precedence <= PREC_ASSIGNMENT;
  prefixRule(canAssign);

  while (precedence <= getRule(parser.current.type)->precedence) {
    advance();
    ParseFn infixRule = getRule(parser.previous.type)->infix;
    infixRule(canAssign);
  }

  if (canAssign && match(TOKEN_EQUAL)) {
    error("Invalid assignment target.");
  }
}

static ParseRule *getRule(TokenType type) { return &rules[type]; }

static void expression() { parsePrecedence(PREC_ASSIGNMENT); }

static void block() {
  while (!check(TOKEN_RIGHT_BRACE) && !check(TOKEN_EOF)) {
    declaration();
  }

  consume(TOKEN_RIGHT_BRACE, "Expect '}' after block.");
}

static void function(FunctionType type) {
  Compiler compiler;
  initCompiler(&compiler, type);
  beginScope();

  consume(TOKEN_LEFT_PAREN, "Expect '(' after function name.");
  if (!check(TOKEN_RIGHT_PAREN)) {
    do {
      current->function->arity++;
      if (current->function->arity > 255) {
        errorAtCurrent("Can't have more than 255 parameters.");
      }
      uint8_t constant = parseVariable("Expect parameter name.", VAR);
      defineVariable(constant, VAR);
    } while (match(TOKEN_COMMA));
  }

  consume(TOKEN_RIGHT_PAREN, "Expect ')' after parameters.");
  consume(TOKEN_LEFT_BRACE, "Expect '{' before function body.");
  block();

  ObjFunction *function = endCompiler();
  emitBytes(OP_CONSTANT, makeConstant(OBJ_VAL(function)));
}

static void funDeclaration() {
  uint8_t global = parseVariable("Expect function name", NONE);
  markInitialized();
  function(TYPE_FUNCTION);
  defineVariable(global, NONE);
}

static void printStatement() {
  expression();
  consume(TOKEN_SEMICOLON, "Expect ';' after value.");
  emitByte(OP_PRINT);
}

static void returnStatement() {
  if (current->type == TYPE_SCRIPT) {
    error("Can't return from top-level code.");
  }

  if (match(TOKEN_SEMICOLON)) {
    emitReturn();
  } else {
    expression();
    consume(TOKEN_SEMICOLON, "Expect ';' after return value.");
    emitByte(OP_RETURN);
  }
}

static void whileStatement() {
  int loopStart = currentChunk()->count;
  consume(TOKEN_LEFT_PAREN, "Expect '(' after 'while'.");
  expression();
  consume(TOKEN_RIGHT_PAREN, "Expect ')' after condition.");

  int exitJump = emitJump(OP_JUMP_IF_FALSE);
  emitByte(OP_POP);
  statement();

  if (hasBreak != 0) {
    patchJump(hasBreak, 1);
    hasBreak = 0;
  }
  emitLoop(loopStart);

  patchJump(exitJump, 0);
  emitByte(OP_POP);
}

static void synchronize() {
  parser.panicMode = false;

  while (parser.current.type != TOKEN_EOF) {
    if (parser.previous.type == TOKEN_SEMICOLON)
      return;
    switch (parser.current.type) {
    case TOKEN_CLASS:
    case TOKEN_FUN:
    case TOKEN_VAR:
    case TOKEN_FOR:
    case TOKEN_IF:
    case TOKEN_WHILE:
    case TOKEN_PRINT:
    case TOKEN_RETURN:
      return;

    default:; // Do nothing.
    }

    advance();
  }
}

static void expressionStatement() {
  expression();
  consume(TOKEN_SEMICOLON, "Expect ';' after expression");
  emitByte(OP_POP);
}

void switchCase() {
  expression();
  consume(TOKEN_COLONS, "Expect ':' after case expression");

  int caseJump = emitJump(OP_JUMP_SWITCH);

  statement();

  patchJump(caseJump, 0);
}

static void switchStatement() {
  beginScope();
  consume(TOKEN_LEFT_PAREN, "Expect '(' after 'switch'.");
  expression();
  consume(TOKEN_RIGHT_PAREN, "Expect ')' after condition.");
  consume(TOKEN_LEFT_BRACE, "Expect '{' after switch condition");

  while (match(TOKEN_CASE)) {
    switchCase();
  }

  if (match(TOKEN_DEFAULT)) {
    consume(TOKEN_COLONS, "Expect ':' after 'default'.");
    int defaultJump = emitJump(OP_JUMP_DEFAULT);
    statement();
    patchJump(defaultJump, 0);
  }

  emitByte(OP_POP);
  consume(TOKEN_RIGHT_BRACE, "Expect '}'");

  endScope();
}

static void forStatement() {
  beginScope();
  consume(TOKEN_LEFT_PAREN, "Expect '(' after 'for'.");
  if (match(TOKEN_SEMICOLON)) {
  } else if (match(TOKEN_VAR)) {
    variableDeclaration(VAR);
  } else if (match(TOKEN_CONST)) {
    variableDeclaration(CONST);
  } else {
    expressionStatement();
  }

  int loopStart = currentChunk()->count;
  int exitJump = -1;
  if (!match(TOKEN_SEMICOLON)) {
    expression();
    consume(TOKEN_SEMICOLON, "Expect ';'. after loop condition");

    // Jump out of the loop if the condition is false
    exitJump = emitJump(OP_JUMP_IF_FALSE);
    emitByte(OP_POP); // condition
  }

  if (!match(TOKEN_RIGHT_PAREN)) {
    int bodyJump = emitJump(OP_JUMP);
    int incrementStart = currentChunk()->count;
    expression();
    emitByte(OP_POP);
    consume(TOKEN_RIGHT_PAREN, "Expect ')' after for clauses.");

    emitLoop(loopStart);
    loopStart = incrementStart;
    patchJump(bodyJump, 0);
  }

  statement();

  if (hasBreak != 0) {
    patchJump(hasBreak, 1);
    hasBreak = 0;
  }
  emitLoop(loopStart);

  if (exitJump != -1) {
    patchJump(exitJump, 0);
    emitByte(OP_POP);
  }
  endScope();
}

static void ifStatement() {
  consume(TOKEN_LEFT_PAREN, "Expect '(' after 'if'.");
  expression();
  consume(TOKEN_RIGHT_PAREN, "Expect ')' after condition.");

  int thenJump = emitJump(OP_JUMP_IF_FALSE);
  emitByte(OP_POP);
  statement();

  int elseJump = emitJump(OP_JUMP);

  patchJump(thenJump, 0);
  emitByte(OP_POP);

  if (match(TOKEN_ELSE))
    statement();
  patchJump(elseJump, 0);
}

static void breakStatement() {
  hasBreak = emitJump(OP_JUMP);
  consume(TOKEN_SEMICOLON, "Expect ';' after break statement");
}

static void variableDeclaration(Type type) {
  uint8_t global = parseVariable("Expect variable name.", type);

  if (match(TOKEN_EQUAL)) {
    expression();
  } else {
    emitByte(OP_NIL);
  }

  consume(TOKEN_SEMICOLON, "Expect ';' after variable declaration.");

  defineVariable(global, type);
}

static void declaration() {
  if (match(TOKEN_VAR)) {
    variableDeclaration(VAR);
  } else if (match(TOKEN_FUN)) {
    funDeclaration();
  } else if (match(TOKEN_CONST)) {
    variableDeclaration(CONST);
  } else {
    statement();
  }

  if (parser.panicMode)
    synchronize();
}

static void statement() {
  if (match(TOKEN_PRINT)) {
    printStatement();
  } else if (match(TOKEN_IF)) {
    ifStatement();
  } else if (match(TOKEN_RETURN)) {
    returnStatement();
  } else if (match(TOKEN_BREAK)) {
    breakStatement();
  } else if (match(TOKEN_CONTINUE)) {
    /* TODO CONTINUE; */
    printf("/* TODO:  <12-11-22, daniel> todo continue statement*/");
  } else if (match(TOKEN_WHILE)) {
    whileStatement();
  } else if (match(TOKEN_FOR)) {
    forStatement();
  } else if (match(TOKEN_SWITCH)) {
    switchStatement();
  } else if (match(TOKEN_LEFT_BRACE)) {
    beginScope();
    block();
    endScope();
  } else {
    expressionStatement();
  }
}

ObjFunction *compile(const char *source) {
  initScanner(source);
  Compiler compiler;
  initCompiler(&compiler, TYPE_SCRIPT);

  parser.hadError = false;
  parser.panicMode = false;

  advance();

  while (!match(TOKEN_EOF)) {
    declaration();
  }

  ObjFunction *function = endCompiler();
  return parser.hadError ? NULL : function;
}
