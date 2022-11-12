#ifndef clox_table_h
#define clox_table_h

#include "common.h"
#include "value.h"

typedef enum {
  UNDEFINED,
  UNASSINGABLE,
  OK,
} Kind;

typedef struct {
  ObjString *key;
  Value value;
  Type type;
} Entry;

typedef struct {
  int count;
  int capacity;
  Entry *entries;
} Table;

void initTable(Table *table);
void freeTable(Table *table);
bool tableGet(Table *table, ObjString *key, Value *value);
bool tableSet(Table *table, ObjString *key, Value value);
Kind tableSetVariable(Table *table, ObjString *key, Value value, Type type,
                      int kind);
void tableAddAll(Table *from, Table *to);
bool tableDelete(Table *table, ObjString *key);
ObjString *tableFindString(Table *table, const char *chars, int length,
                           uint32_t hash);
#endif
