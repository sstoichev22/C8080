#include <stdio.h>
#include <time.h>

int main(void) {
    time_t start = time();
    //21 seconds for a million
    for (uint32 i = 0; i < 1000000; i++) {}
    time_t end = time();
    printf("%f seconds\n", difftime(end, start));
    return 0;
}
