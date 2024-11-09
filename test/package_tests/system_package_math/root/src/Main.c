#include <math.h>
#include <stdio.h>

int main()
{
    // use volatile to prevent compiler computing sqrt(x) at compile time
    // (we want to force it to link with the sqrt function from the math library)
    volatile double x = 4.0;
    printf("sqrt(4.0) = %.2f\n", sqrt(x));
}
