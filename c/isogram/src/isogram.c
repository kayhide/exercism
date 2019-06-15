#include "isogram.h"
#include <stdint.h>
#include <ctype.h>


bool is_isogram(const char phrase[])
{
  if(!phrase) return false;

  // Make sure `bits` to be longer than 26 bits.
  uint32_t bits = 0;

  for (int i = 0; phrase[i] != 0; ++i) {
    const char c = tolower(phrase[i]);
    if (islower(c)) {
      const int b = 1 << (c - 'a');
      if (bits & b) return false;
      bits |= b;
    }
  }
  return true;
}
