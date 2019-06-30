#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "word_count.h"


void validate_non_null(const void *p) {
  if (p == NULL) {
    perror("NULL pointer");
    exit(EXIT_FAILURE);
  }
}

// Returns index of inserted / tried to insert.
int insert(const char *text, word_count_word_t * words) {
  validate_non_null(text);
  validate_non_null(words);

  int i = 0;
  for (; i < MAX_WORDS; ++i) {
    if ((words[i].text[0] == '\0' && strcpy(words[i].text, text)) ||
        (strcmp(words[i].text, text) == 0)) {
      words[i].count += 1;
      break;
    }
  }
  return i;
}

char* strsep(char **buf, const char *delims) {
  validate_non_null(buf);
  validate_non_null(delims);

  char *p = (char *)*buf;
  if (*p == 0) { return NULL; }
  while (*p && !strchr(delims, *p)) { ++p; }

  char *head = (char *)*buf;
  *p = 0;
  *buf = p + 1;
  return head;
}

int count_words(const word_count_word_t * words) {
  validate_non_null(words);

  int i = 0;
  while (i < MAX_WORDS && (words[i].text[0])) { ++i; }
  return i;
}

int word_count(const char *input_text, word_count_word_t * words) {
  validate_non_null(input_text);
  validate_non_null(words);

  memset(words, 0, sizeof(word_count_word_t) * MAX_WORDS);

  char *buf = malloc(strlen(input_text) + 1);
  validate_non_null(buf);

  strcpy(buf, input_text);
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
      if (insert(token, words) >= MAX_WORDS) { return EXCESSIVE_NUMBER_OF_WORDS; }
    }
  }

  return count_words(words);
}
