#include <stdio.h>
#include <string.h>

void Console_print(char *str_buf)
{
    char *str;
    memcpy(&str, str_buf, sizeof(char*));
    fputs(str, stdout);
}

void Console_println(char *str_buf)
{
    char *str;
    memcpy(&str, str_buf, sizeof(char*));
    puts(str);
}
