/** @file
 * @brief Implementacja kalkulatora.
 *
 * Implementacja kalkulatora działającego na wielomianach rzadkich wielu zmiennych
 * i stosującego odwrotną notację polską
 * @author Zofia Ogonek <zo429578@students.mimuw.edu.pl>
 * @copyright Uniwersytet Warszawski
 * @date 2021
*/

#include "poly.h"

#include <stdio.h>
#include <stdlib.h>
#include <malloc.h>
#include <stddef.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include <limits.h>

/**
  * Początkowy rozmiar bufora wiersza.
  */
#define INITIAL_line_SIZE 32

/**
  * Znak kratki.
  */
#define NUMBER_SIGN '#'

/**
  * Białe znaki.
  */
#define WHITE_SPACES " \t\n\v\f\r"

/**
  * Znak nawiasu otwierającego.
  */
#define OPENING_BRACKET '('

/**
  * Znak nawiasu zamykającego.
  */
#define CLOSING_BRACKET ')'

/**
  * Znak plusa.
  */
#define PLUS '+'

/**
  * Znak minusa.
  */
#define MINUS '-'

/**
  * Znak przecinka.
  */
#define COMMA ','

/**
  * Znak przejścia do nowego wiersza.
  */
#define NEWLINE '\n'

/**
  * Znak spacji.
  */
#define SPACE ' '

/**
  * Początkowy rozmiar tablicy jednomianów wielomianu.
  */
#define INITIAL_ARRAY_SIZE 5

/**
  * Początkowy rozmiar stosu wielomianów.
  */
#define INITIAL_STACK_SIZE 16

/**
  * Polecenie ZERO ze znakiem przejścia do nowego wiersza.
  */
#define ZERO "ZERO\n"

/**
  * Polecenie IS_COEFF ze znakiem przejścia do nowego wiersza.
  */
#define IS_COEFF "IS_COEFF\n"

/**
  * Polecenie IS_ZERO ze znakiem przejścia do nowego wiersza.
  */
#define IS_ZERO "IS_ZERO\n"

/**
  * Polecenie CLONE ze znakiem przejścia do nowego wiersza.
  */
#define CLONE "CLONE\n"

/**
  * Polecenie ADD ze znakiem przejścia do nowego wiersza.
  */
#define ADD "ADD\n"

/**
  * Polecenie MUL ze znakiem przejścia do nowego wiersza.
  */
#define MUL "MUL\n"

/**
  * Polecenie NEG ze znakiem przejścia do nowego wiersza.
  */
#define NEG "NEG\n"

/**
  * Polecenie SUB ze znakiem przejścia do nowego wiersza.
  */
#define SUB "SUB\n"

/**
  * Polecenie IS_EQ ze znakiem przejścia do nowego wiersza.
  */
#define IS_EQ "IS_EQ\n"

/**
  * Polecenie DEG ze znakiem przejścia do nowego wiersza.
  */
#define DEG "DEG\n"

/**
  * Polecenie DEG_BY.
  */
#define DEG_BY "DEG_BY"

/**
  * Polecenie AT.
  */
#define AT "AT"

/**
  * Polecenie PRINT ze znakiem przejścia do nowego wiersza.
  */
#define PRINT "PRINT\n"

/**
  * Polecenie POP ze znakiem przejścia do nowego wiersza.
  */
#define POP "POP\n"

/**
  * Polecenie COMPOSE.
  */
#define COMPOSE "COMPOSE"

/**
  * Makro sprawdzające, czy wskaźnik nie jest pusty.
  * @param[in] p : wskaźnik
  */
#define CHECK_PTR(p)  \
  do {                \
    if (p == NULL) {  \
      exit(1);        \
    }                 \
  } while (0)

/**
 * To jest struktura przechowująca stos wielomianów typu Poly.
 */
typedef struct Stack {
    size_t size; ///< rozmiar stosu (tablicy wielomianów)
    size_t index; ///< indeks w tablicy wielomianów, na który w miarę potrzeby zostanie dodany następny wielomian
    /**
    * To jest tablica przechowująca listę wielomianów.
    */
    struct Poly *array;
} Stack;

/**
 * Inicjalizuje stos wielomianów.
 * @param[in] stack : niezainicjowany stos wielomianów
 */
static void StackInit(Stack *stack) {
    stack->size = INITIAL_STACK_SIZE;
    stack->index = 0;
    stack->array = malloc(stack->size * sizeof(Poly));
    CHECK_PTR(stack->array);
}

/**
 * Sprawdza, czy stos wielomianów jest pełny.
 * @param[in] stack : stos wielomianów
 * @return Czy stos wielomianów jest pełny?
 */
static bool StackIsFull(Stack *stack) {
    return stack->index == stack->size;
}

/**
 * Sprawdza, czy stos wielomianów jest pusty.
 * @param[in] stack : stos wielomianów
 * @return Czy stos wielomianów jest pusty?
 */
static bool StackIsEmpty(Stack *stack) {
    return stack->index == 0;
}

/**
 * Zwraca wielomian na szczycie stosu.
 * @param[in] stack : stos wielomianów
 * @return wielomian na szczycie stosu
 */
static Poly StackTop(Stack *stack) {
    assert(!StackIsEmpty(stack));
    return stack->array[stack->index - 1];
}

/**
 * Zwraca wartość wyrażenia 2n dla danej liczby @p n.
 * @param[in] n : liczba @f$n@f$ typu size_t
 * @return @f$2n@f$
 */
static size_t Increase(size_t n) {
    return 2 * n;
}

/**
 * Powiększa dwuktronie obszar pamięci zarezerwowany dla tablicy wielomianów
 * w stosie wielomianów.
 * Powiększa rozmiar tablicy wielomianów stosu @p stack,
 * a następnie zwiększa obszar pamięci tablicy wielomianów.
 * @param[in] stack : stos wielomianów
 */
static void DoubleTheAmountOfPolysOnStack(Stack *stack) {
    stack->size = Increase(stack->size);
    stack->array = realloc(stack->array, stack->size * sizeof(Poly));
    CHECK_PTR(stack->array);
}

/**
 * W miarę potrzeby powiększa dwuktronie obszar pamięci zarezerwowany
 * dla tablicy wielomianów w stosie wielomianów.
 * Wywoływana przed wstawieniem wielomianu na stos, czyli do tablicy
 * wielomianów w stosie @p stack.
 * @param[in] stack : stos wielomianów.
 */
static void DoubleTheAmountOfPolysOnStackIfNecessary(Stack *stack) {
    if (StackIsFull(stack)) {
        DoubleTheAmountOfPolysOnStack(stack);
    }
}

/**
 * Wstawia wielomian @p p na szczyt stosu wielomianów @p stack.
 * @param[in] stack : stos wielomianów
 * @param[in] p : wielomian, który zostanie wstawiony na szczyt stosu @p stack
 */
static void StackPush(Stack *stack, Poly p) {
    DoubleTheAmountOfPolysOnStackIfNecessary(stack);
    stack->array[stack->index] = p;
    stack->index++;
}

/**
 * Zdejmuje wielomian ze szczytu stosu wielomianów i go zwraca.
 * @param[in] stack : stos wielomianów
 * @return wielomian na szczycie stosu
 */
static Poly StackPop(Stack *stack) {
    Poly p = StackTop(stack);
    stack->index--;
    return p;
}

/**
 * Sprawdza, czy liczba wielomianów na stosie wielomianów jest mniejsza niż dwa.
 * @param[in] stack : stos wielomianów
 * @return Czy liczba wielomianów na stosie jest mniejsza niż dwa?
 */
static bool StackHasLessThanTwoPolys(Stack *stack) {
    return stack->index < 2;
}

/**
 * Sprawdza, czy liczba wielomianów na stosie wielomianów jest mniejsza niż @p k.
 * @param[in] stack : stos wielomianów
 * @param[in] k : wartość parametru @p k
 * @return Czy liczba wielomianów na stosie jest mniejsza niż @p k?
 */
static bool StackHasLessThanKPolys(Stack *stack, size_t k) {
    return stack->index < k;
}

/**
 * Opróżnia stos wielomianów i usuwa z pamięci wszystkie wielomiany, jakie na nim są.
 * Zwalnia też obszar pamięci zarezerwowany dla jego tablicy wielomianów.
 * @param[in] stack : stos wielomianów
 */
static void StackDestroy(Stack *stack) {
    if (!StackIsEmpty(stack)) {
        for (size_t i = 0; i < stack->index; ++i) {
            PolyDestroy(&stack->array[i]);
        }
    }
    free(stack->array);
}

/**
 * Sprawdza, czy znak jest cyfrą lub minusem.
 * @param[in] ch : znak
 * @return Czy znak jest cyfrą lub minusem?
 */
static bool IsADigitOrAMinus(char ch) {
    return isdigit(ch) || ch == MINUS;
}

/**
 * Zwraca pierwszy znak w łańcuchu znaków @p s.
 * @param[in] s : łańcuch znaków
 * @return pierwszy znak w łańcuchu znaków
 */
static char FirstCharacter(const char *s) {
    return s[0];
}

/**
 * Konwertuje wartość zapisaną w łańcuchu znaków @p s w dziesiętnym systemie
 * liczbowym do postaci liczby całkowitej typu poly_coeff_t.
 * Przerywa proces konwersji w chwili napotkania znaku, który nie jest częścią
 * liczby.
 * Adres tego znaku zapisuje do argumentu wyjściowego @p end_ptr.
 * Sprawdza, czy przekonwertowana wartość jest poprawnym współczynnikiem jednomianu.
 * @param[in] s : łańcuch znaków, który ma zostać przekonwertowany do postaci
 * liczbowej
 * @param[in] end_ptr : argument wyjściowy, do którego zostanie zapisany adres
 * pierwszego znaku, którego nie udało się przekonwertować
 * @return Czy przekonwertowana wartość jest poprawnym współczynnikiem jednomianu?
 */
static bool HasACorrectCoeff(const char *s, char **end_ptr) {
    errno = 0;
    poly_coeff_t value_coeff = strtol(s, end_ptr, 10);
    if (errno != ERANGE && value_coeff <= LLONG_MAX && value_coeff >= LLONG_MIN) {
        return true;
    } else {
        return false;
    }
}

/**
 * Konwertuje wartość zapisaną w łańcuchu znaków @p s w dziesiętnym systemie
 * liczbowym do postaci liczby całkowitej typu poly_exp_t.
 * Przerywa proces konwersji w chwili napotkania znaku, który nie jest częścią
 * liczby.
 * Adres tego znaku zapisuje do argumentu wyjściowego @p end_ptr.
 * Sprawdza, czy przekonwertowana wartość jest poprawnym wykładnikiem jednomianu.
 * @param[in] s : łańcuch znaków, który ma zostać przekonwertowany do postaci
 * liczbowej
 * @param[in] end_ptr : argument wyjściowy, do którego zostanie zapisany adres
 * pierwszego znaku, którego nie udało się przekonwertować
 * @return Czy przekonwertowana wartość jest poprawnym wykładnikiem jednomianu?
 */
static bool HasACorrectExp(const char *s, char **end_ptr) {
    errno = 0;
    poly_exp_t value_exp = (poly_exp_t) strtol(s, end_ptr, 10);
    if (errno != ERANGE && value_exp >= 0) {
        return true;
    } else {
        return false;
    }
}

/**
 * Sprawdza, czy łańcuch znaków @p s reprezentuje poprawny wielomian niebędący stałą.
 * Wielomian może być jednomianem lub sumą jednomianów. Parsuje łańcuch znaków @p s
 * do napotkania znaku @p end_char.
 * Funkcja pomocnicza funkcji IsACorrectNonConstantPoly.
 * @param[in] s : łańcuch znaków
 * @param[in] end_char : znak, do którego napotkania jest dokonywane parsowanie
 * łańcucha znaków @p s
 * @return Czy łańcuch znaków @p s reprezentuje poprawny wielomian niebędący stałą?
 */
static bool IsACorrectNonConstantPolyHelper(char **s, char end_char) {
    if (*s == NULL) return false;
    /* Licznik nawiasów otwierających na początku łańcuch znaków. */
    int opening_brackets_counter = 0;
    while (FirstCharacter(*s) != end_char) {
        /* Każdy wielomian niebędący stałą musi rozpoczynać się nawiasem otwierającym. */
        if (FirstCharacter(*s) != OPENING_BRACKET) {
            return false;
        }
        while (FirstCharacter(*s) == OPENING_BRACKET) {
            opening_brackets_counter++;
            (*s)++;
        }
        /* Po nawiasach otwierających powinien wystąpić potencjalny współczynnik.
         * Jeśli aktualny znak nie jest cyfrą lub minusem, łańcuch znaków nie jest
         * poprawnym wielomianem. */
        if (!IsADigitOrAMinus(FirstCharacter(*s))) {
            return false;
        }
        /* Sprawdzamy poprawność współczynnika. */
        char *end_ptr = *s;
        if (!HasACorrectCoeff(*s, &end_ptr)) {
            return false;
        }
        /* Aktualizujemy wartość wskaźnika. */
        *s = end_ptr;
        /* W poprawnym wielomianie powinno wystąpić tyle wykładników, ile
         * wczytaliśmy nawiasów otwierających. */
        for (int i = 0; i < opening_brackets_counter; i++) {
            /* Po współczynniku powinien wystąpić przecinek. */
            if (FirstCharacter(*s) != COMMA) {
                return false;
            }
            (*s)++;
            /* Po przecinku powinien wystąpić potencjalny wykładnik.
             * Jeśli aktualny znak nie jest cyfrą, łańcuch znaków nie
             * jest poprawnym wielomianem. */
            if (!isdigit(FirstCharacter(*s))) {
                return false;
            }
            /* Sprawdzamy poprawność wykładnika. */
            end_ptr = *s;
            if (!HasACorrectExp(*s, &end_ptr)) {
                return false;
            }
            /* Aktualizujemy wartość wskaźnika. */
            *s = end_ptr;
            /* Po wykładniku powinien wystąpić nawias zamykający. */
            if (FirstCharacter(*s) != CLOSING_BRACKET) {
                return false;
            }
            (*s)++;
            /* Możliwe, że dany wielomian jest sumą jednomianów. */
            while (FirstCharacter(*s) == PLUS) {
                (*s)++;
                char next_end_char;
                if (end_char == COMMA || i != opening_brackets_counter - 1) {
                    /* Jeśli aktualnie parsujemy łańcuch znaków do napotkania znaku
                     * przecinka, to przy dalszym sprawdzaniu poprawności łańcucha
                     * znaków nie ulegnie to zmianie. Taka sytuacja będzie miała
                     * miejsce na przykład gdy współczynnik danego wielomianu jest
                     * sumą więcej niż dwóch jednomianów. Jeśli aktualne zagłębienie
                     * nie jest najbardziej zewnętrznym, to również będziemy parsować
                     * łańcuch znaków do napotkania znaku przecinka. */
                    next_end_char = COMMA;
                } else {
                    /* W przeciwnym przypadku będziemy parsować łańcuch znaków do
                     * napotkania znaku przejścia do nowego wiersza. */
                    next_end_char = NEWLINE;
                }
                /* Sprawdzamy poprawność składnika sumy. */
                if (!IsACorrectNonConstantPolyHelper(s, next_end_char)) {
                    return false;
                }
            }
        }
    }
    return true;
}

/**
 * Sprawdza, czy wiersz @p line reprezentuje poprawny wielomian niebędący stałą.
 * Wielomian może być jednomianem lub sumą jednomianów.
 * @param[in] line : łańcuch znaków
 * @return Czy łańcuch znaków @p s reprezentuje poprawny wielomian niebędący stałą?
 */
static bool IsACorrectNonConstantPoly(char *line) {
    /* Wywołujemy funkcję pomoniczą - będziemy parsować łańcuch znaków
     * do napotkania znaku przejścia do nowego wiersza. */
    return IsACorrectNonConstantPolyHelper(&line, NEWLINE);
}

/**
 * Konwertuje wartość zapisaną w łańcuchu znaków @p s w dziesiętnym systemie
 * liczbowym do postaci liczby całkowitej typu poly_coeff_t.
 * Przerywa proces konwersji w chwili napotkania znaku, który nie jest częścią
 * liczby.
 * Adres tego znaku zapisuje do argumentu wyjściowego @p end_ptr.
 * Zwraca przekonwertowaną wartość.
 * @param[in] s : łańcuch znaków, który ma zostać przekonwertowany do postaci
 * współczynnika jednomianu
 * @param[in] end_ptr : argument wyjściowy, do którego zostanie zapisany adres
 * pierwszego znaku, którego nie udało się przekonwertować
 * @return przekonwertowana wartość
 */
static poly_coeff_t MakeCoeff(char *s, char **end_ptr) {
    poly_coeff_t coeff = strtol(s, end_ptr, 10);
    return coeff;
}

/**
 * Konwertuje wartość zapisaną w łańcuchu znaków @p s w dziesiętnym systemie
 * liczbowym do postaci liczby całkowitej typu poly_exp_t.
 * Przerywa proces konwersji w chwili napotkania znaku, który nie jest częścią
 * liczby.
 * Adres tego znaku zapisuje do argumentu wyjściowego @p end_ptr.
 * Zwraca przekonwertowaną wartość.
 * @param[in] s : łańcuch znaków, który ma zostać przekonwertowany do postaci
 * wykładnika jednomianu
 * @param[in] end_ptr : argument wyjściowy, do którego zostanie zapisany adres
 * pierwszego znaku, którego nie udało się przekonwertować
 * @return przekonwertowana wartość
 */
static poly_exp_t MakeExp(char *s, char **end_ptr) {
    poly_exp_t exp = (poly_exp_t) strtol(s, end_ptr, 10);
    return exp;
}

static Poly CreatePolyHelper(char **s, char end_char);

/**
 * Konwertuje wartość zapisaną w łańcuchu znaków @p s do postaci jednomianu
 * typu Mono.
 * Zwraca stworzony jednomian.
 * @param[in] s : łańcuch znaków, który ma zostać przekonwertowany do postaci
 * jednomianu
 * @return stworzony jednomian
 */
static Mono CreateMono(char **s) {
    /* Jednomian zaczyna się nawiasem otwierającym. */
    (*s)++;
    Poly coeff;
    if (FirstCharacter(*s) == OPENING_BRACKET) {
        /* Jeśli aktualnym znakiem jest nawias otwierający, współczynnik jednomianu
         * jest wielomianem nad kolejną zmienną. Parsujemy łańcuch znaków do napotkania
         * znaku przecinka, ponieważ wielomian jest zagłębiony. */
        coeff = CreatePolyHelper(s, COMMA);
    } else {
        /* W przeciwnym przypadku współczynnik jednomianu jest liczbą całkowitą.
         * Wczytujemy ją i tworzymy z niej wielomian stały, który będzie współczynnikiem
         * danego jednomianu. Następnie aktualizujemy wartość wskaźnika. */
        char *end_ptr = *s;
        coeff = PolyFromCoeff(MakeCoeff(*s, &end_ptr));
        *s = end_ptr;
    }
    /* Po współczynniku występuje przecinek. */
    (*s)++;
    /* Wczytujemy liczbę całkowitą będącą wykładnikiem jednomianu. Następnie
     * aktualizujemy wartość wskaźnika. */
    char *end_ptr = *s;
    poly_exp_t exp = MakeExp(*s, &end_ptr);
    *s = end_ptr;
    /* Po wykładniku wystepuje nawias zamykający. */
    (*s)++;
    return (Mono) {.p = coeff, .exp = exp};
}

/**
 * Powiększa dwuktronie obszar pamięci zarezerwowany dla tablicy jednomianów @p arr.
 * Powiększa rozmiar tablicy jednomianów @p size, a następnie zwiększa obszar
 * pamięci tablicy jednomianów.
 * @param[in] arr : tablica jednomianów
 * @param[in] size : rozmiar tablicy jednomianów @p arr
 */
static void DoubleTheAmountOfMonos(Mono **arr, size_t *size) {
    *size = Increase(*size);
    *arr = realloc(*arr, *size * sizeof(Mono));
    CHECK_PTR(*arr);
}

/**
 * W miarę potrzeby powiększa dwuktronie obszar pamięci zarezerwowany dla tablicy
 * jednomianów @p arr.
 * Wywoływana przed wstawieniem jednomianu na indeks @p index do tablicy jednomianów
 * @p arr o rozmiarze @p size.
 * @param[in] arr : tablica jednomianów
 * @param[in] size : rozmiar tablicy jednomianów @p arr
 * @param[in] index : indeks, na który zostanie wstawiony jednomian
 */
static void DoubleTheAmountOfMonosIfNecessary(Mono **arr, size_t *size, size_t index) {
    if (index == *size) {
        DoubleTheAmountOfMonos(arr, size);
    }
}

/**
 * Konwertuje wartość zapisaną w łańcuchu znaków @p s do postaci wielomianu
 * typu Poly.
 * Parsuje łańcuch znaków @p s do napotkania znaku @p end_char.
 * Funkcja pomocnicza funkcji CreatePoly.
 * Zwraca stworzony wielomian.
 * @param[in] s : łańcuch znaków, który ma zostać przekonwertowany do postaci
 * wielomianu
 * @param[in] end_char : znak, do którego napotkania jest dokonywane parsowanie
 * łańcucha znaków @p s
 * @return stworzony wielomian
 */
static Poly CreatePolyHelper(char **s, char end_char) {
    /* Tworzymy tablicę jednomianów tworzonego wielomianu.
     * Jeśli wielomian składa się tylko z jednego jednomianu,
     * tablica pozostanie niezainicjowana i pusta. */
    Mono *arr;
    /* Indeks, na który w miarę potrzeby zostanie wstawiony
     * następny jednomian do tablicy jednomianów arr. */
    size_t index = 0;
    /* Zmienna mówiąca o tym, czy wczytywany wielomian składa
     * się z więcej niż jednego jednomianu. */
    bool HasMoreThanOneMono = false;
    /* Pierwszy jednomian, który na pewno wystąpi. */
    Mono first_mono;
    while (FirstCharacter(*s) != end_char) {
        /* Tworzymy pierwszy jednomian. */
        first_mono = CreateMono(s);
        /* Możliwe, że dany wielomian jest sumą jednomianów. Wtedy
         * inicjalizujemy tablicę arr, wstawiamy do niej jednomian
         * first_mono i wczytujemy następne jednomiany, uzupełniając
         * zawartość tablicy jednomianów arr. */
        if (FirstCharacter(*s) == PLUS) {
            HasMoreThanOneMono = true;
            /* Inicjalizujemy tablicę arr. */
            size_t size = INITIAL_ARRAY_SIZE;
            arr = malloc(size * sizeof(Mono));
            CHECK_PTR(arr);
            /* Wstawiamy pierwszy wczytany jednomian. */
            arr[index] = first_mono;
            index++;
            /* Wczytujemy resztę jednomianów i uzupełniamy
             * zawartość tablicy. */
            while (FirstCharacter(*s) == PLUS) {
                (*s)++;
                DoubleTheAmountOfMonosIfNecessary(&arr, &size, index);
                arr[index] = CreateMono(s);
                index++;
            }
        }
    }
    if (HasMoreThanOneMono) {
        /* Zwracamy wielomian stworzony z utworzonej tablicy jednomianów. */
        Poly p = PolyAddMonos(index, arr);
        free(arr);
        return p;
    } else {
        /* Zwracamy wielomian stworzony z pierwszego jednomianu. */
        const Mono mono[] = {first_mono};
        return PolyAddMonos(1, mono);
    }
}

/**
 * Konwertuje wartość zapisaną w wierszu @p line do postaci wielomianu
 * typu Poly niebędącego stałą.
 * Zwraca stworzony wielomian.
 * @param[in] line : line
 * @return stworzony wielomian
 */
static Poly CreatePoly(char *line) {
    Poly p = CreatePolyHelper(&line, NEWLINE);
    return p;
}

/**
 * Wstawia na wierzchołek stosu wielomian tożsamościowo równy zeru.
 * @param[in] stack : stos wielomianów
 */
static void Zero(Stack *stack) {
    StackPush(stack, PolyZero());
}

/**
 * Sprawdza, czy wielomian na wierzchołku stosu jest współczynnikiem – wypisuje
 * na standardowe wyjście 0 lub 1.
 * Jeśli na stosie jest za mało wielomianów,
 * aby wykonać polecenie, wypisuje odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void Is_Coeff(Stack *stack, int line_number) {
    if (StackIsEmpty(stack)) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackTop(stack);
        if (PolyIsCoeff(&p)) {
            printf("1\n");
        } else {
            printf("0\n");
        }
    }
}

/**
 * Sprawdza, czy wielomian na wierzchołku stosu jest tożsamościowo równy zeru
 * – wypisuje na standardowe wyjście 0 lub 1.
 * Jeśli na stosie jest za mało wielomianów, aby wykonać polecenie, wypisuje
 * odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void Is_Zero(Stack *stack, int line_number) {
    if (StackIsEmpty(stack)) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackTop(stack);
        if (PolyIsZero(&p)) {
            printf("1\n");
        } else {
            printf("0\n");
        }
    }
}

/**
 * Wstawia na stos kopię wielomianu z wierzchołka.
 * Jeśli na stosie jest za mało wielomianów, aby wykonać polecenie, wypisuje
 * odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void Clone(Stack *stack, int line_number) {
    if (StackIsEmpty(stack)) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackTop(stack);
        StackPush(stack, PolyClone(&p));
    }
}

/**
 * Dodaje dwa wielomiany z wierzchu stosu, usuwa je i wstawia na wierzchołek
 * stosu ich sumę.
 * Jeśli na stosie jest za mało wielomianów, aby wykonać polecenie, wypisuje
 * odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void Add(Stack *stack, int line_number) {
    if (StackHasLessThanTwoPolys(stack)) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackPop(stack);
        Poly q = StackPop(stack);
        StackPush(stack, PolyAdd(&p, &q));
        PolyDestroy(&p);
        PolyDestroy(&q);
    }
}

/**
 * Mnoży dwa wielomiany z wierzchu stosu, usuwa je i wstawia na wierzchołek
 * stosu ich iloczyn.
 * Jeśli na stosie jest za mało wielomianów, aby wykonać polecenie, wypisuje
 * odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void Mul(Stack *stack, int line_number) {
    if (StackHasLessThanTwoPolys(stack)) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackPop(stack);
        Poly q = StackPop(stack);
        StackPush(stack, PolyMul(&p, &q));
        PolyDestroy(&p);
        PolyDestroy(&q);
    }
}

/**
 * Neguje wielomian na wierzchołku stosu.
 * Jeśli na stosie jest za mało wielomianów, aby wykonać polecenie, wypisuje
 * odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void Neg(Stack *stack, int line_number) {
    if (StackIsEmpty(stack)) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackPop(stack);
        StackPush(stack, PolyNeg(&p));
        PolyDestroy(&p);
    }
}

/**
 * Odejmuje od wielomianu z wierzchołka wielomian pod wierzchołkiem,
 * usuwa je i wstawia na wierzchołek stosu różnicę.
 * Jeśli na stosie jest za mało wielomianów, aby wykonać polecenie, wypisuje
 * odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void Sub(Stack *stack, int line_number) {
    if (StackHasLessThanTwoPolys(stack)) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackPop(stack);
        Poly q = StackPop(stack);
        StackPush(stack, PolySub(&p, &q));
        PolyDestroy(&p);
        PolyDestroy(&q);
    }
}

/**
 * Sprawdza, czy dwa wielomiany na wierzchu stosu są równe – wypisuje na
 * standardowe wyjście 0 lub 1.
 * Jeśli na stosie jest za mało wielomianów, aby wykonać polecenie, wypisuje
 * odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void Is_Eq(Stack *stack, int line_number) {
    if (StackHasLessThanTwoPolys(stack)) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackPop(stack);
        Poly q = StackTop(stack);
        if (PolyIsEq(&p,&q)) {
            printf("1\n");
        } else {
            printf("0\n");
        }
        StackPush(stack, p);
    }
}

/**
 * Wypisuje na standardowe wyjście stopień wielomianu (−1 dla wielomianu
 * tożsamościowo równego zeru).
 * Jeśli na stosie jest za mało wielomianów, aby wykonać polecenie, wypisuje
 * odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void Deg(Stack *stack, int line_number) {
    if (StackIsEmpty(stack)) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackTop(stack);
        printf("%d\n", PolyDeg(&p));
    }
}

/**
 * Wypisuje na standardowe wyjście stopień wielomianu ze względu na zmienną
 * o numerze @p idx (−1 dla wielomianu tożsamościowo równego zeru).
 * Jeśli na stosie jest za mało wielomianów, aby wykonać polecenie, wypisuje
 * odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] idx : numer zmiennej, ze względu na którą jest wypisywany na
 * standardowe wyjście stopień wielomianu
 * @param[in] line_number : numer wiersza
 */
static void Deg_By(Stack *stack, size_t idx, int line_number) {
    if (StackIsEmpty(stack)) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackTop(stack);
        printf("%d\n", PolyDegBy(&p, idx));
    }
}

/**
 * Wylicza wartość wielomianu w punkcie @p x, usuwa wielomian z wierzchołka
 * i wstawia na stos wynik operacji.
 * Jeśli na stosie jest za mało wielomianów, aby wykonać polecenie, wypisuje
 * odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] x : punkt, w którym jest wyliczana wartość wielomianu
 * @param[in] line_number : numer wiersza
 */
static void At(Stack *stack, poly_coeff_t x, int line_number) {
    if (StackIsEmpty(stack)) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackPop(stack);
        StackPush(stack, PolyAt(&p, x));
        PolyDestroy(&p);
    }
}

static void PolyPrint(Poly p);

/**
 * Wypisuje na standardowe wyjście jednomian @p m.
 * @param[in] m : jednomian
 */
static void MonoPrint(Mono m) {
    PolyPrint(m.p);
    printf(",%d", m.exp);
}

/**
 * Wypisuje na standardowe wyjście wielomian @p p.
 * @param[in] p : wielomian
 */
static void PolyPrint(Poly p) {
    if (PolyIsCoeff(&p)) {
        printf("%ld",p.coeff);
    } else {
        for (size_t i = 0; i < p.size; i++) {
            printf("(");
            MonoPrint(p.arr[i]);
            printf(")");
            if (i != p.size - 1) {
                printf("+");
            }
        }
    }
}

/**
 * Wypisuje na standardowe wyjście wielomian z wierzchołka stosu.
 * Jeśli na stosie jest za mało wielomianów, aby wykonać polecenie, wypisuje
 * odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void Print(Stack *stack, int line_number) {
    if (StackIsEmpty(stack)) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackTop(stack);
        PolyPrint(p);
        printf("\n");
    }
}

/**
 * Usuwa wielomian z wierzchołka stosu.
 * Jeśli na stosie jest za mało wielomianów, aby wykonać polecenie, wypisuje
 * odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void Pop(Stack *stack, int line_number) {
    if (StackIsEmpty(stack)) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackPop(stack);
        PolyDestroy(&p);
    }
}

/**
 * Zdejmuje z wierzchołka stosu najpierw wielomian @p p, a potem kolejno wielomiany
 * @p q[k - 1], @p q[k - 2], …, @p q[0] i umieszcza na stosie wynik operacji złożenia.
 * Jeśli na stosie jest za mało wielomianów, aby wykonać polecenie, wypisuje
 * odpowiedni komunikat błędu.
 * @param[in] stack : stos wielomianów
 * @param[in] k : rozmiar tablicy zmiennych
 * @param[in] line_number : numer wiersza
 */
static void Compose(Stack *stack, size_t k, int line_number) {
    /* Żeby operacja była możliwa, na stosie powinno się znajować
     * k + 1 wielomianów (k w tablicy q[] oraz wielomian p). */
    if (StackHasLessThanKPolys(stack, k + 1) || k == ULONG_MAX) {
        fprintf(stderr, "ERROR %d STACK UNDERFLOW\n", line_number);
    } else {
        Poly p = StackPop(stack);
        Poly *q = calloc(k, sizeof(Poly));
        CHECK_PTR(q);
        for (size_t i = 0; i < k; ++i) {
            q[k - i - 1] = StackPop(stack);
        }
        StackPush(stack, PolyCompose(&p, k, q));
        PolyDestroy(&p);
        for (size_t i = 0; i < k; ++i) {
            PolyDestroy(&q[i]);
        }
        free(q);
    }
}

/**
 * Sprawdza, czy wiersz jest pusty.
 * @param[in] line : wiersz
 * @return Czy wiersz jest pusty?
 */
static bool LineIsEmpty(char *line) {
    return strcmp(line, "\n") == 0 || strcmp(line, "") == 0;
}

/**
 * Sprawdza, czy wiersz ma być zignorowany.
 * @param[in] line : wiersz
 * @return Czy wiersz ma być zignorowany?
 */
static bool LineIsToBeIgnored(char *line) {
    return LineIsEmpty(line) || FirstCharacter(line) == NUMBER_SIGN;
}

/**
 * Sprawdza, czy wiersz zaczyna się literą, nawiasem otwierającym, cyfrą
 * lub minusem.
 * @param[in] line : wiersz
 * @return Czy wiersz zaczyna się literą, nawiasem otwierającym, cyfrą
 * lub minusem?
 */
static bool LineBeginsWithALetterOrAnOpeningBracketOrADigitOrAMinus(char *line) {
    return isalpha(FirstCharacter(line)) || FirstCharacter(line) == OPENING_BRACKET ||
            isdigit(FirstCharacter(line)) || FirstCharacter(line) == MINUS;
}

/**
 * Dodaje znak przejścia do nowego wiersza na koniec wiersza.
 * @param[in] line : wiersz
 */
static void AddNewlineCharacterAtTheEndOfLine(char **line) {
    strcat(*line, "\n");
}

/**
 * Jeśli wiersz nie kończy się znakiem przejścia do nowego wiersza, dodaje go.
 * @param[in] line : wiersz
 */
static void AddNewlineCharacterAtTheEndOfLineIfNecessary(char *line) {
    if (line[strlen(line) - 1] != NEWLINE) {
        AddNewlineCharacterAtTheEndOfLine(&line);
    }
}

/**
 * Sprawdza, czy w wierszu znajdują się tylko białe znaki.
 * @param[in] line : wiersz
 * @return Czy w wierszu znajdują się tylko białe znaki?
 */
static bool LineHasOnlyWhitespace(const char *line) {
    for (size_t i = 0; line[i]; i++) {
        if (!isspace(line[i])) {
            return false;
        }
    }
    return true;
}

/**
 * Sprawdza, czy w wierszu znajduje się tylko jedno słowo (łańcuch znaków)
 * oraz nie ma w nim żadnych białych znaków oprócz znaku przejścia do
 * nowego wiersza na końcu.
 * @param[in] line : wiersz
 * @return Czy w wierszu znajduje się tylko jedno słowo (łańcuch znaków)
 * oraz nie ma w nim żadnych białych znaków oprócz znaku przejścia do
 * nowego wiersza na końcu?
 */
static bool LineHasOnlyOneWordAndNoWhitespacesExceptNewline(const char *line) {
    return strcspn(line, WHITE_SPACES) == strlen(line) - 1;
}

/**
 * Sprawdza, czy wiersz zaczyna się literą alfabetu angielskiego.
 * @param[in] line : wiersz
 * @return Czy wiersz zaczyna się literą alfabetu angielskiego?
 */
static bool LineBeginsWithALetter(const char *line) {
    return isalpha(FirstCharacter(line));
}

/**
 * Sprawdza, czy wiersz zaczynający się literą alfabetu angielskiego
 * zaczyna się małą literą alfabetu angielskiego.
 * @param[in] line : wiersz
 * @return Czy wiersz zaczynający się literą alfabetu angielskiego
 * zaczyna się małą literą alfabetu angielskiego?
 */
static bool LineBeginsWithALowercaseLetter(char *line) {
    return FirstCharacter(line) == tolower(FirstCharacter(line));
}

/**
 * Sprawdza, czy wczytany wiersz @p line to polecenie @p command.
 * @param[in] command : polecenie
 * @param[in] line : wczytane polecenie
 * @return Czy wczytany wiersz @p line to polecenie @p command?
 */
static bool TheCommandIs(char *command, char *line) {
    return strcmp(command, line) == 0;
}

/**
 * Sprawdza, czy wczytany wiersz z jednym słowem zawiera poprawne polecenie.
 * Sprawdza, czy wczytane polecenie @p line ma poprawną nazwę i jeśli tak,
 * to wykonuje je.
 * Jeśli polecenie jest niepoprawne, wypisuje odpowiedni komunikat błędu.
 * @param[in] line : wczytany wiersz
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void CheckLineWithOneWordAndAPossibleCommand(char *line, Stack *stack,
                                                    int line_number) {
    if (LineBeginsWithALowercaseLetter(line)) {
        fprintf(stderr, "ERROR %d WRONG COMMAND\n", line_number);
    } else if (TheCommandIs(ZERO, line)) {
        Zero(stack);
    } else if (TheCommandIs(IS_COEFF, line)) {
        Is_Coeff(stack, line_number);
    } else if (TheCommandIs(IS_ZERO, line)) {
        Is_Zero(stack, line_number);
    } else if (TheCommandIs(CLONE, line)) {
        Clone(stack, line_number);
    } else if (TheCommandIs(ADD, line)) {
        Add(stack, line_number);
    } else if (TheCommandIs(MUL, line)) {
        Mul(stack, line_number);
    } else if (TheCommandIs(NEG, line)) {
        Neg(stack, line_number);
    } else if (TheCommandIs(SUB, line)) {
        Sub(stack, line_number);
    } else if (TheCommandIs(IS_EQ, line)) {
        Is_Eq(stack, line_number);
    } else if (TheCommandIs(DEG, line)) {
        Deg(stack, line_number);
    } else if (TheCommandIs(PRINT, line)) {
        Print(stack, line_number);
    } else if (TheCommandIs(POP, line)) {
        Pop(stack, line_number);
    } else if (TheCommandIs("DEG_BY\n", line)) {
        fprintf(stderr, "ERROR %d DEG BY WRONG VARIABLE\n", line_number);
    } else if (TheCommandIs("AT\n", line)) {
        fprintf(stderr, "ERROR %d AT WRONG VALUE\n", line_number);
    } else if (TheCommandIs("COMPOSE\n", line)) {
        fprintf(stderr, "ERROR %d COMPOSE WRONG PARAMETER\n", line_number);
    } else {
        fprintf(stderr, "ERROR %d WRONG COMMAND\n", line_number);
    }
}

/**
 * Zwraca przedostatni znak w łańcuchu znaków @p s.
 * @param[in] s : łańcuch znaków
 * @return przedostatni znak w łańcuchu znaków
 */
static char PenultimateCharacter(char *s) {
    return s[strlen(s) - 2];
}

/**
 * Sprawdza, czy wiersz rozpoczyna się otwierającym nawiasem i kończy zamykającym
 * (nie licząc znaku nowej linii).
 * @param[in] line : wiersz
 * @return Czy wiersz rozpoczyna się otwierającym nawiasem i kończy zamykającym
 * (nie licząc znaku nowej linii)?
 */
static bool LineBeginsWithAnOpeningBracketAndEndsWithAClosingOne(char *line) {
    return FirstCharacter(line) == OPENING_BRACKET &&
            PenultimateCharacter(line) == CLOSING_BRACKET;
}

/**
 * Sprawdza, czy wczytany wiersz z jednym słowem jest poprawnym wielomianem
 * niebędącym stałą i jeśli tak, to wstawia go na szczyt stosu @p stack.
 * Jeśli wielomian jest niepoprawny, wypisuje odpowiedni komunikat błędu.
 * @param[in] line : wczytany wiersz
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void CheckLineWithOneWordAndPossibleNonConstantPoly(char *line, Stack *stack,
                                                           int line_number) {
    if (IsACorrectNonConstantPoly(line)) {
        StackPush(stack, CreatePoly(line));
    } else {
        fprintf(stderr, "ERROR %d WRONG POLY\n", line_number);
    }
}

/**
 * Sprawdza, czy wczytany łańcuch znaków @p s jest poprawnym współczynnikiem
 * wielomianu stałego lub parametrem polecenia AT. Zapisuje jego wartość
 * do zmiennej @p value.
 * @param[in] s : wczytany łańcuch znaków
 * @param[in] value : wartość współczynnika lub parametru polecenia AT
 * @return Czy wczytany łańcuch znaków jest poprawnym współczynnikiem
 * wielomianu stałego lub parametrem polecenia AT?
 */
static bool IsACorrectConstantPolyOrAtValue(char *s, poly_coeff_t *value) {
    char *end_ptr = s;
    errno = 0;
    *value = strtol(s, &end_ptr, 10);
    return !(s == end_ptr || *end_ptr != NEWLINE || errno == ERANGE) &&
            *value <= LLONG_MAX && *value >= LLONG_MIN &&
            IsADigitOrAMinus(FirstCharacter(s));
}

/**
 * Sprawdza, czy wczytany wiersz z jednym słowem jest poprawnym wielomianem
 * będącym stałą i jeśli tak, to wstawia go na szczyt stosu @p stack.
 * Jeśli wielomian jest niepoprawny, wypisuje odpowiedni komunikat błędu.
 * @param[in] line : wczytany wiersz
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void CheckLineWithOneWordAndPossibleConstantPoly(char *line, Stack *stack,
                                                        int line_number) {
    poly_coeff_t value;
    if (IsACorrectConstantPolyOrAtValue(line, &value)) {
        StackPush(stack, PolyFromCoeff(value));
    } else {
        fprintf(stderr, "ERROR %d WRONG POLY\n", line_number);
    }
}

/**
 * Sprawdza, czy wczytany łańcuch znaków @p s jest poprawnym parametrem
 * polecenia "DEG_BY" lub "COMPOSE". Zapisuje jego wartość do zmiennej @p value.
 * @param[in] s : wczytany łańcuch znaków
 * @param[in] value : wartość parametru polecenia "DEG_BY" lub "COMPOSE"
 * @return Czy wczytany łańcuch znaków jest poprawnym parametrem
 * polecenia "DEG_BY" lub "COMPOSE"?
 */
static bool IsACorrectDegByOrComposeValue(char *s, size_t *value) {
    char *end_ptr = s;
    errno = 0;
    *value = strtoul(s, &end_ptr, 10);
    return !(s == end_ptr || *end_ptr != NEWLINE || errno == ERANGE) &&
            *value <= ULONG_MAX && isdigit(FirstCharacter(s));
}

/**
 * Sprawdza, czy wiersz @p line zaczynający się poleceniem "DEG_BY"
 * po tym poleceniu ma znak spacji i cyfrę.
 * @param[in] line : wiersz
 * @return Czy wiersz @p line zaczynający się poleceniem "DEG_BY"
 * po tym poleceniu ma znak spacji i cyfrę?
 */
static bool HasASpaceAndADigitAfterDegByCommand(const char *line) {
    return line[sizeof(DEG_BY) - 1] == SPACE && isdigit(line[sizeof(DEG_BY)]);
}

/**
 * Sprawdza, czy wiersz @p line zaczynający się poleceniem "DEG_BY"
 * po tym poleceniu ma biały znak.
 * @param[in] line : wiersz
 * @return Czy wiersz @p line zaczynający się poleceniem "DEG_BY"
 * po tym poleceniu ma biały znak?
 */
static bool HasAWhitespaceAfterDegByCommand(const char *line) {
    return isspace(line[sizeof(DEG_BY) - 1]);
}

/**
 * Sprawdza, czy wczytany wiersz z poleceniem "DEG_BY" zawiera poprawny
 * parametr i jeśli tak, to wykonuje je polecenie "DEG_BY" z tym parameterm.
 * Jeśli parametr jest niepoprawny, wypisuje odpowiedni komunikat błędu.
 * @param[in] line : wiersz
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void CheckLineWithAPossibleDegByCommand(char *line, Stack *stack,
                                               int line_number) {
    if (!HasASpaceAndADigitAfterDegByCommand(line)) {
        if (HasAWhitespaceAfterDegByCommand(line)) {
            fprintf(stderr, "ERROR %d DEG BY WRONG VARIABLE\n", line_number);
        } else {
            fprintf(stderr, "ERROR %d WRONG COMMAND\n", line_number);
        }
    } else {
        /* Sprawdzamy poprawność parametru występującego po poleceniu "DEG_BY" oraz
         * znaku spacji. */
        line += sizeof(DEG_BY);
        size_t value;
        if (IsACorrectDegByOrComposeValue(line, &value)) {
            Deg_By(stack, value, line_number);
        } else {
            fprintf(stderr, "ERROR %d DEG BY WRONG VARIABLE\n", line_number);
        }
    }
}

/**
 * Sprawdza, czy wiersz @p line zaczynający się poleceniem "AT"
 * po tym poleceniu ma znak spacji i cyfrę lub minus.
 * @param[in] line : wiersz
 * @return Czy wiersz @p line zaczynający się poleceniem "AT"
 * po tym poleceniu ma znak spacji i cyfrę lub minus?
 */
static bool HasASpaceAndADigitOrAMinusAfterAtCommand(const char *line) {
    return line[sizeof(AT) - 1] == SPACE &&
            (isdigit(line[sizeof(AT)]) || line[sizeof(AT)] == MINUS);
}

/**
 * Sprawdza, czy wiersz @p line zaczynający się poleceniem "AT"
 * po tym poleceniu ma biały znak.
 * @param[in] line : wiersz
 * @return Czy wiersz @p line zaczynający się poleceniem "AT"
 * po tym poleceniu ma biały znak?
 */
static bool HasAWhitespaceAfterAtCommand(const char *line) {
    return isspace(line[sizeof(AT) - 1]);
}

/**
 * Sprawdza, czy wczytany wiersz z poleceniem "AT" zawiera poprawny
 * parametr i jeśli tak, to wykonuje je polecenie "AT" z tym parameterm.
 * Jeśli parametr jest niepoprawny, wypisuje odpowiedni komunikat błędu.
 * @param[in] line : wiersz
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void CheckLineWithAPossibleAtCommand(char *line, Stack *stack,
                                            int line_number) {
    if (!HasASpaceAndADigitOrAMinusAfterAtCommand(line)) {
        if (HasAWhitespaceAfterAtCommand(line)) {
            fprintf(stderr, "ERROR %d AT WRONG VALUE\n", line_number);
        } else {
            fprintf(stderr, "ERROR %d WRONG COMMAND\n", line_number);
        }
    } else {
        /* Sprawdzamy poprawność parametru występującego po poleceniu "AT" oraz
         * znaku spacji. */
        line += sizeof(AT);
        poly_coeff_t value;
        if (IsACorrectConstantPolyOrAtValue(line, &value)) {
            At(stack, value, line_number);
        } else {
            fprintf(stderr, "ERROR %d AT WRONG VALUE\n", line_number);
        }
    }
}

/**
 * Sprawdza, czy wiersz @p line zaczynający się poleceniem "COMPOSE"
 * po tym poleceniu ma znak spacji i cyfrę.
 * @param[in] line : wiersz
 * @return Czy wiersz @p line zaczynający się poleceniem "COMPOSE"
 * po tym poleceniu ma znak spacji i cyfrę?
 */
static bool HasASpaceAndADigitAfterComposeCommand(const char *line) {
    return line[sizeof(COMPOSE) - 1] == SPACE && isdigit(line[sizeof(COMPOSE)]);
}

/**
 * Sprawdza, czy wiersz @p line zaczynający się poleceniem "COMPOSE"
 * po tym poleceniu ma biały znak.
 * @param[in] line : wiersz
 * @return Czy wiersz @p line zaczynający się poleceniem "COMPOSE"
 * po tym poleceniu ma biały znak?
 */
static bool HasAWhitespaceAfterComposeCommand(const char *line) {
    return isspace(line[sizeof(COMPOSE) - 1]);
}

/**
 * Sprawdza, czy wczytany wiersz z poleceniem "COMPOSE" zawiera poprawny
 * parametr i jeśli tak, to wykonuje je polecenie "COMPOSE" z tym parameterm.
 * Jeśli parametr jest niepoprawny, wypisuje odpowiedni komunikat błędu.
 * @param[in] line : wiersz
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void CheckLineWithAPossibleComposeCommand(char *line, Stack *stack,
                                               int line_number) {
    if (!HasASpaceAndADigitAfterComposeCommand(line)) {
        if (HasAWhitespaceAfterComposeCommand(line)) {
            fprintf(stderr, "ERROR %d COMPOSE WRONG PARAMETER\n", line_number);
        } else {
            fprintf(stderr, "ERROR %d WRONG COMMAND\n", line_number);
        }
    } else {
        /* Sprawdzamy poprawność parametru występującego po poleceniu "COMPOSE" oraz
         * znaku spacji. */
        line += sizeof(COMPOSE);
        size_t value;
        if (IsACorrectDegByOrComposeValue(line, &value)) {
            Compose(stack, value, line_number);
        } else {
            fprintf(stderr, "ERROR %d COMPOSE WRONG PARAMETER\n", line_number);
        }
    }
}

/**
 * Sprawdza, czy łańcuch znaków @p a rozpoczyna się łańcuchem znaków @p b.
 * @param[in] a : sprawdzany łańcuch znaków
 * @param[in] b : łańcuch znaków, którym być może rozpoczyna się @p a
 * @return : Czy łańcuch znaków @p a rozpoczyna się łańcuchem znaków @p b?
 */
bool StartsWith(const char *a, const char *b) {
    if (strncmp(a, b, strlen(b)) == 0) return true;
    return false;
}

/**
 * Sprawdza, czy wczytany wiersz z więcej niż jednym słowem zawiera poprawne
 * polecenie i jeśli tak, to wykonuje je.
 * Jeśli polecenie jest niepoprawne, wypisuje odpowiedni komunikat błędu.
 * @param[in] line : wiersz
 * @param[in] stack : stos wielomianów
 * @param[in] line_number : numer wiersza
 */
static void CheckLineWithMoreThanOneWordAndAPossibleCommand(char *line, Stack *stack,
                                                            int line_number) {
    if (StartsWith(line, DEG_BY)) {
        CheckLineWithAPossibleDegByCommand(line, stack, line_number);
    } else if (StartsWith(line, AT)) {
        CheckLineWithAPossibleAtCommand(line, stack, line_number);
    } else if (StartsWith(line, COMPOSE)) {
        CheckLineWithAPossibleComposeCommand(line, stack, line_number);
    } else {
        fprintf(stderr, "ERROR %d WRONG COMMAND\n", line_number);
    }
}

/**
 * Czyta dane wierszami ze standardowego wejścia i wykonuje odpowiednie
 * polecenia działające na wielomianach rzadkich wielu zmiennych.
 * Jeśli wczytany wiersz jest niepoprawny, wypisuje odpowiedni komunikat błędu.
 */
static void Calculate() {
    char *line;
    size_t line_size = INITIAL_line_SIZE;
    ssize_t numberOfCharacters;

    line = malloc(line_size * sizeof(char));
    CHECK_PTR(line);

    int line_number = 1;

    Stack stack;
    StackInit(&stack);

    while ((numberOfCharacters = getline(&line, &line_size, stdin)) != -1) {
        if (line == NULL) {
            exit(1);
        }
        if (numberOfCharacters != (ssize_t) strlen(line)) {
            if (LineBeginsWithALetter(line)) {
                if (StartsWith(line, "DEG_BY ")) {
                    fprintf(stderr, "ERROR %d DEG BY WRONG VARIABLE\n", line_number);
                } else if (StartsWith(line, "AT ")) {
                    fprintf(stderr, "ERROR %d AT WRONG VALUE\n", line_number);
                } else if (StartsWith(line, "COMPOSE ")) {
                    fprintf(stderr, "ERROR %d COMPOSE WRONG PARAMETER\n", line_number);
                } else {
                    fprintf(stderr, "ERROR %d WRONG COMMAND\n", line_number);
                }
            } else {
                fprintf(stderr, "ERROR %d WRONG POLY\n", line_number);
            }
        } else if (!LineIsToBeIgnored(line)) {
            /* Nie ignorujemy wiersza. */
            if (!LineBeginsWithALetterOrAnOpeningBracketOrADigitOrAMinus(line)) {
                /* Wiersz nie rozpoczyna się literą, nawiasem otwierającym, cyfrą ani minusem,
                 * więc reprezentuje niepoprawny wielomian. */
                fprintf(stderr, "ERROR %d WRONG POLY\n", line_number);
            } else {
                AddNewlineCharacterAtTheEndOfLineIfNecessary(line);
                if (LineHasOnlyWhitespace(line)) {
                    /* Wiersz zawiera same białe znaki. */
                    fprintf(stderr, "ERROR %d WRONG POLY\n", line_number);
                } else if (LineHasOnlyOneWordAndNoWhitespacesExceptNewline(line)) {
                    /* Wiersz zawiera jedno słowo oraz nie ma w nim żadnych białych znaków oprócz
                     * znaku przejścia do nowego wiersza na końcu. */
                    if (LineBeginsWithALetter(line)) {
                        /* Wiersz zawiera jedno słowo i rozpoczyna się literą alfabetu angielskiego,
                         * więc może reprezentować polecenie. */
                        CheckLineWithOneWordAndAPossibleCommand(line, &stack, line_number);
                    } else if (LineBeginsWithAnOpeningBracketAndEndsWithAClosingOne(line)) {
                        /* Wiersz zawiera jedno słowo i rozpoczyna się nawiasem otwierającym, a kończy
                         * zamykającym, więc może reprezentować wielomian niebędący stałą. */
                        CheckLineWithOneWordAndPossibleNonConstantPoly(line, &stack, line_number);
                    } else {
                        /* W przeciwnym przypadku, jeśli wiersz zawiera jedno słowo, może reprezentować
                         * wielomian będący stałą. */
                        CheckLineWithOneWordAndPossibleConstantPoly(line, &stack, line_number);
                    }
                } else {
                    if (LineBeginsWithALetter(line)) {
                        /* Wiersz zawiera więcej niż jedno słowo i rozpoczyna się literą alfabetu
                         * angielskiego, więc może reprezentować polecenie. */
                        CheckLineWithMoreThanOneWordAndAPossibleCommand(line, &stack, line_number);
                    } else {
                        /* Wiersz zawiera więcej niż jedno słowo i nie rozpoczyna się literą alfabetu
                         * angielskiego, więc reprezentuje niepoprawny wielomian. */
                        fprintf(stderr, "ERROR %d WRONG POLY\n", line_number);
                    }
                }
            }
        }
        ++line_number;
    }
    StackDestroy(&stack);
    free(line);
}

/**
 * Główna funkcja.
 */
int main() {
    Calculate();
    return 0;
}