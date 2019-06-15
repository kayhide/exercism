#include "acronym.h"
#include <ctype.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>


char *abbreviate(const char *phrase)
{
  if(!phrase || !*phrase) return NULL;

  char *buf = calloc(0, strlen(phrase) + 1);
  char *p = buf;

  bool heading = true;
  for(const char *c = phrase; *c; ++c) {
    if(heading) {
      *p = toupper(*c);
      ++p;
      heading = false;
    } else if(*c  == ' ' || *c == '-'){
      heading = true;
    }
  }
  return buf;
}
