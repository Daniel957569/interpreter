cmake_minimum_required(VERSION 3.25)
project(lol C)

set(CMAKE_C_STANDARD 99)

add_executable(lol main.c debug.c debug.h common.h chunk.c chunk.h memory.c
    memory.h value.c value.h vm.c vm.h compiler.c compiler.h scanner.c
    scanner.h object.c object.h table.c table.h)

