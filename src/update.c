/*
 * update.c - 开源版不含在线更新，这里只保留入口，供 htmlmain.c 链接。
 */
#include <stdio.h>

#include "update.h"

int update_maybe_check(void) { return 0; }

int update_cli(int argc, char **argv)
{
    (void)argc;
    (void)argv;
    fputs("开源版不含在线更新\n", stderr);
    return 1;
}
