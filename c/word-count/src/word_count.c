#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <string.h>
#include "word_count.h"


bool insert(const char *text, word_count_word_t * words) {
  for (int i = 0; i < MAX_WORDS; ++i) {
    if (words[i].text[0] == 0) {
      strcpy(words[i].text, text);
      words[i].count = 1;
      return true;
    }
    if (strcmp(words[i].text, text) == 0) {
      words[i].count += 1;
      return true;
    }
  }
  return false;
}


int word_count(const char *input_text, word_count_word_t * words) {
  memset(words, 0, sizeof(word_count_word_t) * MAX_WORDS);

  {
    char *buf = strdup(input_text);
    char *token;
    while ((token = strsep(&buf, " ,.\n:!&@$%^")) != NULL) {
      int len = strlen(token);
      if (len > 0) {
        if (token[0] == '\'' && token[len - 1] == '\'') {
          token[0] = token[len - 1] = 0;
          token += 1;
        }
        if (strlen(token) > MAX_WORD_LENGTH) { return EXCESSIVE_LENGTH_WORD; }
        for (char *c = token; *c; ++c) {
          *c = tolower(*c);
        }
        if (!insert(token, words)) { return EXCESSIVE_NUMBER_OF_WORDS; }
      }
    }
  }

  {
    int i = 0;
    for (; i < MAX_WORDS; ++i) {
      if (words[i].text[0] == 0) {
        return i;
      }
    }
    return i;
  }
}
