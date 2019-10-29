#include "memstream.h"

#include <stdlib.h>
#include <assert.h>

int main()
{
    char *buffer= 0;
    size_t size= 0;
    FILE *fp= open_memstream(&buffer, &size);
    int i;
    for (i= 0;  i < 10240;  ++i) {
	static char c= 42;
	fflush(fp);			assert(size == i);
	fwrite(&c, 1, 1, fp);
    }
    fclose(fp);				assert(size == 10240);
    free(buffer);
    fp= open_memstream(&buffer, &size);
    fprintf(fp, "This is a test of memstream, from main at %p.\n", main);
    fclose(fp);
    fputs(buffer, stdout);
    free(buffer);
    return 0;
}
