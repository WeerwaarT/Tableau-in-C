#include <stdio.h>
#include <string.h>   /* for all the new-fangled string functions */
#include <stdlib.h>     /* malloc, free, rand */


#define NOT_FMLA 0
#define PROPOSITION 1
#define NEGATION 2
#define BINARY 3


int fSize = 50; /*maximum formula length*/
int inputs = 10;/* number of formulas expected in input2.txt*/
int ThSize = 100;/* maximum size of set of formulas, if needed*/
int TabSize = 500; /*maximum length of tableau queue, if needed*/


/* A set will contain a list of words. Use NULL for empty set.  */
struct set
{
    char *item;/*first word of non-empty set*/
    struct set *tail;/*remaining words in the set*/
};


/* A tableau will contain a list of pointers to sets (of words).  Use NULL for empty list.*/
struct tableau
{
    struct set *S; /* pointer to first set in non-empty list */
    struct tableau *rest; /*list of pointers to other sets*/
};


int parse(const char *);
void partOne(char *, char *);
void partTwo(char *, char *);
int isFormula(const char *, int);
int isProposition(const char *);
int isBinary(const char *, int);
int min(int, int);
void enqueue(struct tableau *, struct set *);
int isFullyExpanded(struct set *);
char getSymbol(char *);
void complete(struct tableau *);
int processOneTableau(struct set *, struct tableau *);
int getType(char *);
int processSet(struct set *s, struct tableau *tTail);
void processDisjunction(struct set *, struct tableau *);
void itemEnqueue(struct set *, char *);
void setCpy(struct set *, struct set *);
void processConjunction(struct set *);
void processAlpha(struct set *);
void processBeta(struct set *, struct tableau *);
int closed(struct tableau *);
int setIsClosed(struct set *);


/* A function to free all the allocated bits on the tableau */
void deepFree(struct tableau *t)
{
    if(!t) return;
    while(t->S)
    {
        // free(t->S->item);
        struct set *tempSet = t->S;
        t->S = t->S->tail;
        free(tempSet);
    }
    struct tableau *tempTableau = t;
    t = t->rest;
    free(tempTableau);
    deepFree(t);
}

int parse(const char *input)
{
    int length = (int) strlen(input);
    switch (*input)
    {
        case 'p':
        case 'q':
        case 'r':   return *(input + 1) == '\0';
        case '-':   return isFormula((input + 1), min(length - 1, fSize - 1))?NEGATION:NOT_FMLA;
        case '(':   return isFormula(input, min(length, fSize))?BINARY:NOT_FMLA;
        default:    return NOT_FMLA;
    }
}

int min(int a, int b)
{
    return (a<b)?a:b;
}

int isFormula(const char *fmla, int length)
{
    if (*fmla == '-')
    {
        return isFormula((fmla + 1), (length - 1));
    }
    switch (length)
    {
        case 0:     return NOT_FMLA;
        case 1:     return isProposition(fmla);
        case 2:
        case 3:
        case 4:     return NOT_FMLA;
        default :   return isBinary(fmla, length);
    }
}

int isBinary(const char *fmla, int length)  // simplest form of a formula except negation and proposition is
{                                           // (proposition BC proposition), its length is 5
    int parenthesesStack = 0;
    int i;
    for (i = 0; i < length; ++i)
    {
        char current = *(fmla + i);
        switch (current)
        {
            case '(': parenthesesStack++; break;
            case ')': parenthesesStack--; break;
            default:  continue;
        }
        if (parenthesesStack < 0)
        {
            return NOT_FMLA;
        }
        if (parenthesesStack == 0 && i != length - 1)
        {
            return NOT_FMLA;
        }
    }
    if (parenthesesStack != 0)
    {
        return NOT_FMLA;
    }

    int binaryConjunctionIsFound = 0;
    int isLookingForBinaryConjunction = 0;
    int sizeOfLeft = 0;
    int leftIsFormula = 0, rightIsFormula;
    while (sizeOfLeft < length)
    {
        char current = *(fmla + sizeOfLeft);
        if (isLookingForBinaryConjunction)
        {
            switch (current)
            {
                case '(': isLookingForBinaryConjunction = 0; break;
                case ')': return NOT_FMLA;
                case '>':
                case 'v':
                case '^': binaryConjunctionIsFound = 1; break;
                case '-':
                case 'p':
                case 'q':
                case 'r': break;
                default:  return NOT_FMLA;
            }
        }
        if (binaryConjunctionIsFound)
        {
            leftIsFormula = isFormula((fmla + 1), (sizeOfLeft - 1));
            rightIsFormula = isFormula((fmla + sizeOfLeft + 1), length - 2 - sizeOfLeft);
            break;
        }
        switch (current)
        {
            case '(': if (++parenthesesStack == 1) isLookingForBinaryConjunction = 1; break;
            case ')': if (--parenthesesStack == 1) isLookingForBinaryConjunction = 1; break;
            case '>':
            case '^':
            case 'v':
            case '-':
            case 'p':
            case 'q':
            case 'r': break;
            default:  return NOT_FMLA;
        }
        ++sizeOfLeft;
    }
    return leftIsFormula && rightIsFormula;
}

int isProposition(const char *fmla)
{
    switch (*fmla)
    {
        case 'p':
        case 'q':
        case 'r': return PROPOSITION;
        default:  return NOT_FMLA;
    }
}

void partOne(char *fmla, char *dest)
{
    int length = (int) strlen(fmla);
    int sizeOfLeft = 0;
    int parenthesesStack = 0;
    int isLookingForBinaryConjunction = 0;
    int keepLooking = 1;
    while (sizeOfLeft < length)
    {
        char current = *(fmla + sizeOfLeft);
        if (isLookingForBinaryConjunction)
        {
            switch (current)
            {
                case '(': isLookingForBinaryConjunction = 0; break;
                case '>':
                case 'v':
                case '^': sizeOfLeft--; keepLooking = 0; break;
                default:  ;
            }
        }
        if (!keepLooking)
        {
            break;
        }
        switch (current)
        {
            case '(': if (++parenthesesStack == 1) isLookingForBinaryConjunction = 1; break;
            case ')': if (--parenthesesStack == 1) isLookingForBinaryConjunction = 1; break;
            default:  ;
        }
        sizeOfLeft++;
    }
    int i,j;
    for (i = 0; i < sizeOfLeft; ++i)
    {
        *(dest + i) = *(fmla + 1 + i);
    }
    for (j = sizeOfLeft; j < strlen(dest); ++j)
    {
        *(dest + j) = '\0';
    }
}

void partTwo(char *fmla, char *dest)
{
    int length = (int) strlen(fmla);
    int sizeOfLeft = 0;
    int parenthesesStack = 0;
    int isLookingForBinaryConjunction = 0;
    int keepLooking = 1;
    while (sizeOfLeft < length)
    {
        char current = *(fmla + sizeOfLeft);
        if (isLookingForBinaryConjunction)
        {
            switch (current)
            {
                case '(': isLookingForBinaryConjunction = 0; break;
                case '>':
                case 'v':
                case '^': keepLooking = 0; break;
                default:  ;
            }
        }
        if (!keepLooking)
        {
            break;
        }
        switch (current)
        {
            case '(': if (++parenthesesStack == 1) isLookingForBinaryConjunction = 1; break;
            case ')': if (--parenthesesStack == 1) isLookingForBinaryConjunction = 1; break;
            default:  ;
        }
        sizeOfLeft++;
    }
    int sizeOfRight = length - 2 - sizeOfLeft;
    int i,j;
    for (i = 0; i < sizeOfRight; ++i)
    {
        *(dest + i) = *(fmla + 1 + sizeOfLeft + i);
    }
    for (j = sizeOfRight; j < strlen(dest); ++j)
    {
        *(dest + j) = '\0';
    }
}

int processOneTableau(struct set *s, struct tableau *tTail)
{
    if (isFullyExpanded(s))
    {
        enqueue(tTail, s);
        return -1;
    }
    else
    {
        return processSet(s, tTail);
    }
}

int processSet(struct set *s, struct tableau *tTail)
{
    int tick = 0;
    while (s)
    {
        switch (getType(s->item))
        {   // alpha = 0, beta = 1, proposition = 2, conjunction = 3, disjunction = 4
            case 0:     processAlpha(s); break;
            case 1:     processBeta(s, tTail); tTail = tTail->rest; ++tick; break;  // ++tick -> tick - 1(this) + 2(new)
            case 2:     itemEnqueue(s->tail, s->item); break;
            case 3:     processConjunction(s); break;
            case 4:     processDisjunction(s, tTail); tTail = tTail->rest; ++tick; break;
            default:    ;
        }
        s = s->tail;
        if (isFullyExpanded(s))
        {
            enqueue(tTail, s);
            return tick;
        }
    }
    return tick;
}

void processBeta(struct set *s, struct tableau *tTail)
{
    if (parse(s->item) == NEGATION)     // -(p^q)
    {
        char *fmla = s->item + 1;
        char *left = calloc(fSize, sizeof(char));
        char *right = calloc(fSize, sizeof(char));
        *left = '-';
        *right = '-';
        partOne(fmla, left + 1);
        partTwo(fmla, right + 1);

        struct set *leftSet = calloc(1, sizeof(struct set));
        leftSet->item = left;
        struct set *rightSet = calloc(1, sizeof(struct set));
        rightSet->item = right;
        if (s->tail)
        {
            setCpy(leftSet, s->tail);
            setCpy(rightSet, s->tail);
            s->tail = NULL;
        }
        enqueue(tTail, leftSet);
        enqueue(tTail->rest, rightSet);
    }
    else                                // (p>q)
    {
        char *fmla = s->item;
        char *left = calloc(fSize, sizeof(char));
        char *right = calloc(fSize, sizeof(char));
        *left = '-';
        partOne(fmla, left + 1);
        partTwo(fmla, right);

        struct set *leftSet = calloc(1, sizeof(struct set));
        leftSet->item = left;
        struct set *rightSet = calloc(1, sizeof(struct set));
        rightSet->item = right;
        if (s->tail)
        {
            setCpy(leftSet, s->tail);
            setCpy(rightSet, s->tail);
            s->tail = NULL;
        }
        enqueue(tTail, leftSet);
        enqueue(tTail->rest, rightSet);
    }
}

void processAlpha(struct set *s)
{
    if (parse((s->item + 1)) == NEGATION)
    {
        itemEnqueue(s, (s->item + 2));
    }
    else if (getSymbol(s->item + 1) == 'v')
    {
        char *left = calloc(fSize, sizeof(char));
        char *right = calloc(fSize, sizeof(char));
        *left = '-';
        *right = '-';
        partOne(s->item + 1, left + 1);
        partTwo(s->item + 1, right + 1);
        itemEnqueue(s, left);
        itemEnqueue(s, right);
    }
    else    // symbol == '>'
    {
        char *left = calloc(fSize, sizeof(char));
        char *right = calloc(fSize, sizeof(char));
        *right = '-';
        partOne(s->item + 1, left);
        partTwo(s->item + 1, right + 1);
        itemEnqueue(s, left);
        itemEnqueue(s, right);
    }
}

void processConjunction(struct set *s)
{
    char *fmla = s->item;
    char *left = calloc(fSize, sizeof(char));
    char *right = calloc(fSize, sizeof(char));
    partOne(fmla, left);
    partTwo(fmla, right);

    itemEnqueue(s, left);
    itemEnqueue(s, right);
}

void processDisjunction(struct set *s, struct tableau *tTail)
{
    char *fmla = s->item;
    char *left = calloc(fSize, sizeof(char));
    char *right = calloc(fSize, sizeof(char));
    partOne(fmla, left);
    partTwo(fmla, right);

    struct set *rightSet = calloc(1, sizeof(struct set));
    rightSet->item = right;
    struct set *leftSet = calloc(1, sizeof(struct set));
    leftSet->item = left;
    if (s->tail)
    {
        setCpy(leftSet, s->tail);
        setCpy(rightSet, s->tail);
        s->tail = NULL;
    }
    enqueue(tTail, leftSet);
    enqueue(tTail->rest, rightSet);
}

void setCpy(struct set *dest, struct set *src)
{
    struct set *destTemp = dest;
    struct set *srcTemp = src;
    while (srcTemp)
    {
        struct set *new = calloc(1, sizeof(struct set));
        new->item = calloc(fSize, sizeof(char));
        strcpy(new->item, srcTemp->item);
        destTemp->tail = new;
        destTemp = destTemp->tail;
        srcTemp = srcTemp->tail;
    }
}

void itemEnqueue(struct set *dest, char *src)
{
    struct set *temp = dest;
    while ((strcmp(src, temp->item) != 0))
    {
        if (!temp->tail)
        {
            struct set *newSet = calloc(1, sizeof(struct set));
            newSet->item = src;
            temp->tail = newSet;
        }
        temp = temp->tail;
    }
}

int getType(char *fmla)     /*return: alpha = 0, beta = 1, proposition = 2, conjunction = 3, disjunction = 4*/
{
    int type = parse(fmla);
    if (  type == PROPOSITION || (type == NEGATION && parse(fmla + 1) == PROPOSITION)  )
    {
        return 2;
    }
    else if (type == BINARY)
    {
        switch (getSymbol(fmla))
        {
            case '>':   return 1;
            case '^':   return 3;
            case 'v':   return 4;
            default:    return -1;
        }
    }
    else    // symbol == '-'
    {
        if (parse(fmla + 1) == NEGATION)
        {
            return 0;
        }
        else
        {
            if (getSymbol(fmla + 1) == 'v' || getSymbol(fmla + 1) == '>')
            {
                return 0;
            }
            else    // symbol == '^'
            {
                return 1;
            }
        }
    }
}

char getSymbol(char *fmla)
{
    char *temp = fmla;
    int parenthesesStack = 0;
    int isLookingForBinaryConjunction = 0;
    int stopLooking = 0;
    while (temp)
    {
        char current = *temp;
        if (isLookingForBinaryConjunction)
        {
            switch (current)
            {
                case '(': isLookingForBinaryConjunction = 0; break;
                case '>':
                case 'v':
                case '^': stopLooking = 1; break;
                default:  ;
            }
        }
        if (stopLooking)
        {
            return *temp;
        }
        switch (current)
        {
            case '(': if (++parenthesesStack == 1) isLookingForBinaryConjunction = 1; break;
            case ')': if (--parenthesesStack == 1) isLookingForBinaryConjunction = 1; break;
            default:  ;
        }
        ++temp;
    }
    return *fmla;
}

int isFullyExpanded(struct set *s)
{
    if (!s)
    {
        return 0;
    }
    struct set *temp = s;
    while (temp)
    {
        int isNegationProposition = *temp->item == '-' && isProposition((temp->item + 1));
        if (!(isProposition(temp->item) || isNegationProposition))
        {
            return 0;
        }
        temp = temp->tail;
    }
    return 1;
}

void enqueue(struct tableau *t, struct set *s)
{
    struct tableau *new = calloc(1, sizeof(struct tableau));
    new->S = s;
    t->rest = new;
}

void complete(struct tableau *t)
{
    int uncheckedTableau = 1;
    struct tableau *tail = t;
    while (uncheckedTableau > 0)
    {
        while (tail->rest)
        {
            tail = tail->rest;
        }
        uncheckedTableau += processOneTableau(t->S, tail);
        *t = *t->rest;
    }
}

int closed(struct tableau *t)
{
    while (t)
    {
        if (!setIsClosed(t->S))
        {
            return 0;
        }
        t = t->rest;
    }
    return 1;
}

int setIsClosed(struct set *s)
{
    while (s)
    {
        struct set *temp = s->tail;
        char *item = s->item;
        if (*item == '-')
        {
            *item = *(item + 1);
            *(item + 1) = '\0';
        }
        else
        {
            *(item + 1) = *item;
            *item = '-';
        }
        while (temp)
        {
            if (strcmp(item, temp->item) == 0)
            {
                return 1;
            }
            temp = temp->tail;
        }
        s = s->tail;
    }
    return 0;
}

int main()
{
    /*input 10 strings from "input.txt" */

    /*You should not need to alter the input and output parts of the program below.*/
    char *name = calloc(fSize, sizeof(char));
    char *left = calloc(fSize, sizeof(char));
    char *right = calloc(fSize, sizeof(char));
    FILE *fp, *fpOut;

    /* reads from input.txt, writes to output.txt*/
    if ( (fp = fopen("input.txt","r")) == NULL )
    {
        printf("Error opening file");
        exit(1);
    }
    if ( (fpOut = fopen("output.txt", "w")) == NULL )
    {
        printf("Error opening file");
        exit(1);
    }
    int j;
    for (j = 0; j < inputs; j++)
    {
        fscanf(fp, "%s", name);/*read formula*/
        switch (parse(name))
        {
            case(0):  fprintf(fpOut, "%s is not a formula.  \n", name);break;
            case(1):  fprintf(fpOut, "%s is a proposition. \n ", name);break;
            case(2):  fprintf(fpOut, "%s is a negation.  \n", name);break;
            case(3):  partOne(name, left);
                      partTwo(name, right);
                      fprintf(fpOut, "%s is a binary. The first part is %s and the second part is %s  \n", name, left, right);
                      break;
            default:  fprintf(fpOut, "What the f***!  ");
        }

        if (parse(name) != 0)
        {
            /* Initialise the tableau with the formula */
            char* s = calloc(fSize, sizeof(char));
            strcpy(s, name);
            struct set* S = calloc(1, sizeof(struct set));
            S->item = s;
            struct tableau* t = calloc(1, sizeof(struct tableau));
            t->S = S;

            /* Completes the tableau and checks if it is closed */
            complete(t);
            if (closed(t))  fprintf(fpOut, "%s is not satisfiable.\n", name);
            else fprintf(fpOut, "%s is satisfiable.\n", name);

            /* Frees all the bits of memory on the tableau*/
            deepFree(t);
        }
        else
        {
            fprintf(fpOut, "I told you, %s is not a formula.\n", name);
        }
    }

    fclose(fp);
    fclose(fpOut);
    free(left);
    free(right);
    free(name);

    return 0;
}
