/** @file
 * @brief Implementacja operacji.
 *
 * Implementacja operacji wielomianów rzadkich wielu zmiennych
 * @author Zofia Ogonek <zo429578@students.mimuw.edu.pl>
 * @copyright Uniwersytet Warszawski
 * @date 2021
*/

#include "poly.h"
#include <stdlib.h>
#include <string.h>
#include <malloc.h>
#include <assert.h>

/**
  * Początkowy rozmiar tablicy jednomianów wielomianu.
  */
#define INITIAL_ARRAY_SIZE 5

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
 * Inicjalizuje tablicę jednomianów wielomianu.
 * @param[in] p : wielomian
 */
static void InitializeMonoArray(Poly *p) {
    p->arr = calloc(p->size, sizeof(Mono));
    CHECK_PTR(p->arr);
}

/**
 * Usuwa wielomian z pamięci.
 * @param[in] p : wielomian
 */
void PolyDestroy(Poly *p) {
    assert(p != NULL);
    /* Jeśli wielomian jest współczynnikiem, to nie trzeba
     * nic usuwać z pamięci. */
    if (!PolyIsCoeff(p)) {
        for (size_t i = 0; i < p->size; ++i) {
            MonoDestroy(&p->arr[i]);
        }
        free(p->arr);
    }
}

/**
 * Robi pełną, głęboką kopię wielomianu.
 * @param[in] p : wielomian
 * @return skopiowany wielomian
 */
Poly PolyClone(const Poly *p) {
    assert(p != NULL);
    if (PolyIsCoeff(p)) {
        return PolyFromCoeff(p->coeff);
    } else {
        Poly clone;
        clone.size = p->size;
        InitializeMonoArray(&clone);
        for (size_t i = 0; i < clone.size; ++i) {
            clone.arr[i] = MonoClone(&p->arr[i]);
        }
        return clone;
    }
}

/**
 * Zwraca wykładnik o mniejszej wartości z dwóch podanych wykładników.
 * @param[in] a : wykładnik
 * @param[in] b : wykładnik
 * @return wykładnik o mniejszej wartości
 */
static poly_exp_t min(poly_exp_t a, poly_exp_t b) {
    if (a < b) {
        return a;
    }
    return b;
}

/**
 * Sprawdza, czy wielomian ma tablicę jednomianów o rozmiarze zero.
 * @param[in] p : wielomian
 * @return Czy wielomian ma tablicę jednomianów o rozmiarze zero?
 */
static bool PolyHasMonoArrayOfSizeZero(const Poly p) {
    return p.size == 0;
}

/**
 * Sprawdza, czy wielomian ma w tablicy jednomianów wyłącznie jeden jednomian,
 * którego współczynnik jest liczbą całkowitą.
 * @param[in] p : wielomian
 * @return czy wielomian ma w tablicy jednomianów wyłącznie jeden jednomian,
 * którego współczynnik jest liczbą całkowitą?
 */
static bool PolyHasOnlyOneMonoWithNumberAsCoeff(const Poly p) {
    return p.size == 1 &&
           p.arr[0].exp == 0 &&
           PolyIsCoeff(&p.arr[0].p);
}

/**
 * Sprawdza, czy wielomian ma w tablicy jednomianów same jednomiany,
 * których współczynniki są wielomianami tożsamościowo równymi zeru.
 * @param[in] p : wielomian
 * @return czy wielomian ma w tablicy jednomianów same jednomiany,
 * których współczynniki są wielomianami tożsamościowo równymi zeru?
 */
static bool PolyHasOnlyPolyZerosAsCoeffsInMonoArray(const Poly p) {
    /* Zliczamy jednomiany w tablicy jednomianów, których współczynniki
     * są wielomianami tożsamościowo równymi zeru. */
    size_t counter_coeff_zero = 0;
    for (size_t i = 0; i < p.size; ++i) {
        if (PolyIsZero(&p.arr[i].p)) {
            ++counter_coeff_zero;
        }
    }
    return counter_coeff_zero == p.size;
}

/**
 * Robi pełną, głęboką kopię tablicy jednomianów wielomianu @p q
 * do tablicy jednomianów wielomianu @p p, zaczynając od drugiego indeksu.
 * @param[in] p : wielomian @f$p@f$, do którego tablica jednomianów zostanie skopiowana
 * @param[in] q : wielomian @f$q@f$, którego tablica jednomianów zostanie skopiowana
 */
static void CloneMonoArrayFromSecondElement(Poly *p, const Poly *q) {
    for (size_t i = 1; i < p->size; ++i) {
        p->arr[i] = MonoClone(&q->arr[i - 1]);
    }
}

/**
 * Robi pełną, głęboką kopię tablicy jednomianów wielomianu @p q,
 * zaczynając od drugiego elementu, do tablicy jednomianów wielomianu @p p,
 * zaczynając od drugiego indeksu.
 * @param[in] p : wielomian @f$p@f$, do którego tablica jednomianów zostanie skopiowana
 * @param[in] q : wielomian @f$q@f$, którego tablica jednomianów zostanie skopiowana
 */
static void CloneMonoArrayFromSecondElementWithoutFirst(Poly *p, const Poly *q) {
    for (size_t i = 1; i < p->size; ++i) {
        p->arr[i] = MonoClone(&q->arr[i]);
    }
}

/**
 * Robi pełną, głęboką kopię tablicy jednomianów wielomianu @p q,
 * zaczynając od drugiego elementu, do tablicy jednomianów wielomianu @p p.
 * @param[in] p : wielomian @f$p@f$, do którego tablica jednomianów zostanie skopiowana
 * @param[in] q : wielomian @f$q@f$, którego tablica jednomianów zostanie skopiowana
 */
static void CloneMonoArrayWithoutFirstElement(Poly *p, const Poly *q) {
    for (size_t i = 0; i < p->size; ++i) {
        p->arr[i] = MonoClone(&q->arr[i + 1]);
    }
}

/**
 * Dodaje do wielomianu @p p niebędącego współczynnikiem, wielomian @p q,
 * który jest współczynnikiem.
 * @param[in] p : wielomian @f$p@f$ niebędący współczynnikiem
 * @param[in] q : wielomian @f$q@f$ będący współczynnikiem
 * @return @f$p + q@f$
 */
Poly PolyAddCoeff(const Poly *p, const Poly *q) {
    Poly sum;
    sum.size = p->size;
    if (p->arr[0].exp != 0) {
        /* Jeśli w tablicy jednomianów p nie ma jednomianu o wykładniku zero,
         * to jako pierwszy element tablicy jednomianów wielomianu sum wstawiamy
         * wielomian stały o współczynniku q i wykładniku zero, a potem
         * kopiujemy tablicę jednomianów wielomianu p. */
        ++sum.size;
        InitializeMonoArray(&sum);
        sum.arr[0] = MonoFromPoly(q,0);
        CloneMonoArrayFromSecondElement(&sum, p);

    } else {
        if (PolyIsCoeff(&p->arr[0].p)) {
            if (p->arr[0].p.coeff + q->coeff != 0) {
                /* Jeśli w tablicy jednomianów p jest jednomian o wykładniku zero,
                 * którego współczynnik jest wielomianem stałym, a suma tego
                 * współczynnika ze współczynnikiem q nie wynosi zero,
                 * to jako pierwszy element tablicy jednomianów wielomianu sum wstawiamy
                 * wielomian stały o współczynniku p+q i wykładniku zero, a potem
                 * kopiujemy resztę tablicy jednomianów wielomianu p. */
                InitializeMonoArray(&sum);
                sum.arr[0] = MonoClone(&p->arr[0]);
                sum.arr[0].p.coeff += q->coeff;
                CloneMonoArrayFromSecondElementWithoutFirst(&sum, p);
            } else {
                /* Jeśli w tablicy jednomianów p jest jednomian o wykładniku zero,
                 * którego współczynnik jest wielomianem stałym, ale suma tego
                 * współczynnika ze współczynnikiem q wynosi zero,
                 * to jako pierwszy element tablicy jednomianów wielomianu sum wstawiamy
                 * drugi element w tablicy jednomianów wielomianu p i dalej
                 * kopiujemy resztę tej tablicy. */
                --sum.size;
                if (PolyHasMonoArrayOfSizeZero(sum)) {
                    /* Jeśli jedynym elementem tablicy jednomianów wielomianu p
                     * był jednomian o wykładniku zero, to zwracamy wielomian
                     * tożsamościowo równy zeru. */
                    PolyDestroy(&sum);
                    return PolyZero();
                }
                InitializeMonoArray(&sum);
                CloneMonoArrayWithoutFirstElement(&sum, p);
            }

        } else {
            Poly coeff_sum = PolyAdd(&p->arr[0].p, q);
            if (!PolyIsZero(&coeff_sum)) {
                /* Jeśli w tablicy jednomianów p jest jednomian o wykładniku zero,
                 * którego współczynnik nie jest wielomianem stałym, a suma tego
                 * współczynnika ze współczynnikiem q nie wynosi zero,
                 * to jako pierwszy element tablicy jednomianów wielomianu sum wstawiamy
                 * wielomian o współczynniku p+q i wykładniku zero, a potem
                 * kopiujemy resztę tablicy jednomianów wielomianu p. */
                InitializeMonoArray(&sum);
                sum.arr[0].p = PolyClone(&coeff_sum);
                sum.arr[0].exp = 0;
                CloneMonoArrayFromSecondElementWithoutFirst(&sum, p);
            } else {
                /* Jeśli w tablicy jednomianów p jest jednomian o wykładniku zero,
                 * którego współczynnik jest wielomianem stałym, ale suma tego
                 * współczynnika ze współczynnikiem q wynosi zero,
                 * to jako pierwszy element tablicy jednomianów wielomianu sum wstawiamy
                 * drugi element w tablicy jednomianów wielomianu p i dalej
                 * kopiujemy resztę tej tablicy. */
                --sum.size;
                if (PolyHasMonoArrayOfSizeZero(sum)) {
                    /* Jeśli jedynym elementem tablicy jednomianów wielomianu p
                     * był jednomian o wykładniku zero, to zwracamy wielomian
                     * tożsamościowo równy zeru. */
                    PolyDestroy(&coeff_sum);
                    PolyDestroy(&sum);
                    return PolyZero();
                }
                InitializeMonoArray(&sum);
                CloneMonoArrayWithoutFirstElement(&sum, p);
            }
            PolyDestroy(&coeff_sum);
        }
    }

    if (PolyHasOnlyOneMonoWithNumberAsCoeff(sum)) {
        poly_coeff_t coeff = sum.arr[0].p.coeff;
        PolyDestroy(&sum);
        return PolyFromCoeff(coeff);
    }

    if (PolyHasOnlyPolyZerosAsCoeffsInMonoArray(sum)) {
        PolyDestroy(&sum);
        return PolyZero();
    }

    return sum;
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
 * Powiększa dwuktronie obszar pamięci zarezerwowany dla tablicy jednomianów w wielomianie.
 * Powiększa rozmiar tablicy jednomianów wielomianu @p p,
 * a następnie zwiększa obszar pamięci tablicy jednomianów.
 * @param[in] p : wielomian
 */
static void DoubleTheAmountOfMonos(Poly *p) {
    p->size = Increase(p->size);
    p->arr = realloc(p->arr, p->size * sizeof(Mono));
    CHECK_PTR(p->arr);
}

/**
 * W miarę potrzeby powiększa dwuktronie obszar pamięci zarezerwowany
 * dla tablicy jednomianów w wielomianie.
 * Wywoływana przed wstawieniem jednomianu na indeks @p index
 * do tablicy jednomianów wielomianu @p p.
 * @param[in] p : wielomian
 * @param[in] index : indeks, na który zostanie wstawiony jednomian
 */
static void DoubleTheAmountOfMonosIfNecessary(Poly *p, size_t index) {
    if (index == p->size) {
        DoubleTheAmountOfMonos(p);
    }
}

/**
 * Wstawia do tablicy jednomianów wielomianu @p p na indeks @p index
 * jednomian o współczynniku @p q niebędącym wielomianem tożsamościowo
 * równym zeru i wykładniku @p exp
 * @param[in] p : wielomian @f$p@f$, do którego tablicy jednomianów zostanie
 * wstawiony jednomian
 * @param[in] index : indeks w tablicy jednomianów wielomianu @p p,
 * na który zostanie wstawiony jednomian
 * @param[in] q : współczynnik wstawianego jednomianu
 * @param[in] exp : wykładnik wstawianego jednomianu
 */
static void PolyAddMono(Poly *p, size_t *index, Poly q, poly_exp_t exp) {
    if (!PolyIsZero(&q)) {
        DoubleTheAmountOfMonosIfNecessary(p, *index);
        Poly q_clone = PolyClone(&q);
        p->arr[*index] = MonoFromPoly(&q_clone, exp);
        ++(*index);
    }
}

/**
 * Wstawia do tablicy jednomianów wielomianu @p p, zaczynając od indeksu @p index_p,
 * kolejne jednomiany będące w tablicy jednomianów wielomianu @p q, zaczynając
 * od indeksu @p index_q
 * @param[in] p : wielomian @f$p@f$, do którego tablicy jednomianów zostaną
 * wstawione jednomiany
 * @param[in] index_p : pierwszy indeks w tablicy jednomianów wielomianu @p p,
 * na który zostanie wstawiony jednomian
 * @param[in] q : wielomian @f$q@f$, z którego tablicy jednomianów zostaną
 * skopiowane jednomiany
 * @param[in] index_q : pierwszy indeks w tablicy jednomianów wielomianu @p q,
 * z którego zostanie skopiowany jednomian
 */
static void PolyAddRemainingMonos(Poly *p, size_t *index_p, Poly q, size_t index_q) {
    for (size_t i = index_q; i < q.size; ++i) {
        PolyAddMono(p, index_p, q.arr[i].p, q.arr[i].exp);
    }
}

/**
 * Dodaje dwa wielomiany.
 * @param[in] p : wielomian @f$p@f$
 * @param[in] q : wielomian @f$q@f$
 * @return @f$p + q@f$
 */
Poly PolyAdd(const Poly *p, const Poly *q) {
    assert(p != NULL);
    assert(q != NULL);

    /* Jeśli któryś z wielomianów p i q jest wielomianem tożsamościowo
     * równym zeru, to zwracamy kopię tego drugiego. */
    if (PolyIsZero(q)) {
        return PolyClone(p);
    }
    if (PolyIsZero(p)) {
        return PolyClone(q);
    }

    if (PolyIsCoeff(p) && PolyIsCoeff(q)) {
        return PolyFromCoeff(p->coeff + q->coeff);
    }

    if (PolyIsCoeff(q)) {
        return PolyAddCoeff(p, q);
    }
    if (PolyIsCoeff(p)) {
        return PolyAddCoeff(q, p);
    }

    /* Wykładnik o największej wartości występujący jako wykładnik
     * jednomianu w tablicy jednomianów wielomianu p. */
    poly_exp_t max_exp_p = p->arr[p->size - 1].exp;
    /* Wykładnik o największej wartości występujący jako wykładnik
     * jednomianu w tablicy jednomianów wielomianu q. */
    poly_exp_t max_exp_q = q->arr[q->size - 1].exp;
    size_t index_p = 0; // Indeks tablicy jednomianów wielomianu p.
    size_t index_q = 0; // Indeks tablicy jednomianów wielomianu q.

    Poly sum;
    sum.size = INITIAL_ARRAY_SIZE;
    sum.arr = malloc(INITIAL_ARRAY_SIZE * sizeof (Mono));
    CHECK_PTR(sum.arr);
    
    size_t index = 0; // Indeks tablicy jednomianów wielomianu sum.
    int i;
    for (i = 0; i <= min(max_exp_p, max_exp_q); ++i) {
        if (p->arr[index_p].exp == i && q->arr[index_q].exp == i) {
            /* Jeśli jednomiany o potędze i występują zarówno w tablicy
             * jednomianów wielomianu p, jak i w tablicy jednomianów
             * wielomianu q, to dodajemy do tablicy jednomianów wielomianu
             * sum ich sumę. */
            Poly coeff_sum = PolyAdd(&p->arr[index_p].p, &q->arr[index_q].p);
            PolyAddMono(&sum, &index, coeff_sum, i);
            PolyDestroy(&coeff_sum);
            ++index_p;
            ++index_q;

        } else if (p->arr[index_p].exp == i) {
            PolyAddMono(&sum, &index, p->arr[index_p].p, i);
            ++index_p;

        } else if (q->arr[index_q].exp == i) {
            PolyAddMono(&sum, &index, q->arr[index_q].p, i);
            ++index_q;
        }
    }

    PolyAddRemainingMonos(&sum, &index, *p, index_p);
    PolyAddRemainingMonos(&sum, &index, *q, index_q);

    sum.size = index;

    if (PolyHasMonoArrayOfSizeZero(sum)) {
        PolyDestroy(&sum);
        return PolyZero();
    }

    if (PolyHasOnlyOneMonoWithNumberAsCoeff(sum)) {
        poly_coeff_t coeff = sum.arr[0].p.coeff;
        PolyDestroy(&sum);
        return PolyFromCoeff(coeff);
    }

    if (PolyHasOnlyPolyZerosAsCoeffsInMonoArray(sum)) {
        PolyDestroy(&sum);
        return PolyZero();
    }

    return sum;
}

/**
 * Porównuje jednomiany, a dokładnie ich wykładniki.
 * Funkcja może zostać wykorzystana w qsorcie.
 * @param[in] a : jednomian
 * @param[in] b : jednomian
 * @return -1, jeśli wykładnik jednomianu @p a jest mniejszy albo
 * 0, jeśli wykładniki jednomianów @p a i @p b są równe albo
 * 1, jeśli wykładnik jednomianu @p b jest mniejszy
 */
int CompareMonos(const void *a, const void *b) {
    const Mono ia = *(const Mono *)a;
    const Mono ib = *(const Mono *)b;
    if (ia.exp < ib.exp) {
        return -1;
    } else if (ia.exp == ib.exp) {
        return 0;
    } else {
        return 1;
    }
}

/**
 * Sprawdza, czy tablica jednomianów ma same jednomiany, których
 * współczynniki są wielomianami tożsamościowo równymi zeru.
 * @param[in] count : liczba jednomianów
 * @param[in] monos : tablica jednomianów
 * @return czy tablica jednomianów ma same jednomiany, których
 * współczynniki są wielomianami tożsamościowo równymi zeru?
 */
static bool MonoArrayHasOnlyPolyZerosAsCoeffs(size_t count, const Mono monos[]) {
    /* Zliczamy jednomiany w tablicy jednomianów, których współczynniki
     * są wielomianami tożsamościowo równymi zeru. */
    size_t count_poly_zeros = 0;
    for (size_t i = 0; i < count; ++i) {
        if (PolyIsZero(&monos[i].p)) {
            ++count_poly_zeros;
        }
    }
    return (count_poly_zeros == count);
}

/**
 * Usuwa elementy tablicy jednomianów z pamięci.
 * @param[in] count : liczba jednomianów
 * @param[in] monos : tablica jednomianów
 */
static void MonoArrayDestroy(size_t count, const Mono monos[]) {
    for (size_t i = 0; i < count; ++i) {
        MonoDestroy((Mono*) &monos[i]);
    }
}

static bool CountIsZeroOrMonosIsNull(size_t count, const Mono monos[]);

/**
 * Sumuje listę jednomianów i tworzy z nich wielomian.
 * Przejmuje na własność zawartość tablicy @p monos.
 * @param[in] count : liczba jednomianów
 * @param[in] monos : tablica jednomianów
 * @return wielomian będący sumą jednomianów
 */
Poly PolyAddMonos(size_t count, const Mono monos[]) {
    if (CountIsZeroOrMonosIsNull(count, monos)) {
        return PolyZero();
    }

    if (MonoArrayHasOnlyPolyZerosAsCoeffs(count, monos)) {
        MonoArrayDestroy(count, monos);
        return PolyZero();
    }

    if (count == 1) {
        if (monos[0].exp == 0 && PolyIsCoeff(&monos[0].p)) {
            poly_coeff_t coeff = monos[0].p.coeff;
            MonoArrayDestroy(count, monos);
            return PolyFromCoeff(coeff);
        }
        Poly p;
        p.size = 1;
        p.arr = malloc(sizeof (Mono));
        CHECK_PTR(p.arr);
        p.arr[0] = MonoClone(&monos[0]);
        MonoArrayDestroy(count, monos);
        return p;
    }

    Mono *monos_copy = malloc(count * sizeof (Mono)); // Płytka kopia tablicy monos.
    CHECK_PTR(monos_copy);
    for (size_t i = 0; i < count; ++i) {
        monos_copy[i] = monos[i];
    }
    /* Sortujemy rosnąco według wykładników kopię tablicy monos. */
    qsort(monos_copy, count, sizeof(Mono), CompareMonos);

    Poly p;
    p.size = INITIAL_ARRAY_SIZE;
    p.arr = malloc(INITIAL_ARRAY_SIZE * sizeof (Mono));
    CHECK_PTR(p.arr);

    size_t index = 0; // Indeks tablicy jednomianów wielomianu p.
    size_t jump; // Przeskok w tablicy jednomianów.
    size_t last_index = count - 1; // Indeks ostatniego jednomianu w tablicy jednomianów monos.

    for (size_t i = 0; i < last_index; i += jump) {
        if (monos_copy[i].exp != monos_copy[i + 1].exp) {
            /* Jeśli wykładnik obecnego jednomianu nie jest równy
             * wykładnikowi następnego, to dodajemy go do tablicy
             * jednomianów wielomianu p i aktualizujemy wartość
             * zmiennej jump na 1. */
            PolyAddMono(&p, &index, monos_copy[i].p, monos_copy[i].exp);
            jump = 1;
        } else {
            /* Jeśli wykładnik obecnego jednomianu jest równy
             * wykładnikowi następnego, to jeśli dotarliśmy do
             * końca tablicy lub jeśli kolejny jednomian ma inny
             * wykładnik, dodajemy ich sumę do tablicy jednomianów.
             * W przeciwnym przypadku tworzymy pomocniczy
             * jednomian sum, do jego współczynnika będziemy
             * dodawać wszystkie współczynniki jednomianów w
             * tablicy jednomianów o tym samym wykładniku.
             * Następnie do tablicy jednomianów dodajemy jednomian
             * sum i aktualizujemy wartość zmiennej jump. */
            if (i + 1 == last_index || monos_copy[i + 1].exp != monos_copy[i + 2].exp) {
                Mono sum;
                sum.p = PolyAdd(&monos_copy[i].p, &monos_copy[i + 1].p);
                sum.exp = monos_copy[i].exp;
                PolyAddMono(&p, &index, sum.p, sum.exp);
                MonoDestroy(&sum);
                jump = 2;
            } else {
                Mono sum;
                sum.p = PolyAdd(&monos_copy[i].p, &monos_copy[i + 1].p);
                sum.exp = monos_copy[i].exp;
                size_t j = i + 1;
                while (j < last_index && monos_copy[j].exp == monos_copy[j + 1].exp) {
                    Poly new_sum = PolyAdd(&sum.p, &monos_copy[j + 1].p);
                    PolyDestroy(&sum.p);
                    sum.p = PolyClone(&new_sum);
                    PolyDestroy(&new_sum);
                    j++;
                }
                PolyAddMono(&p, &index, sum.p, sum.exp);
                MonoDestroy(&sum);
                jump = j - i + 1;
            }
        }
        /* Jeśli dotrzemy do ostatniego jednomianu w tablicy monos,
         * dodajemy go do tablicy jednomianów wielomianu p. */
        if (i + jump == last_index) {
            PolyAddMono(&p, &index, monos_copy[i + jump].p, monos_copy[i + jump].exp);
        }
    }

    /* Aktualizujemy rozmiar tablicy jednomianów wielomianu p. */
    p.size = index;

    if (PolyHasMonoArrayOfSizeZero(p)) {
        PolyDestroy(&p);
        MonoArrayDestroy(count, monos);
        free(monos_copy);
        return PolyZero();
    }

    MonoArrayDestroy(count, monos);
    free(monos_copy);

    if (PolyHasOnlyOneMonoWithNumberAsCoeff(p)) {
        poly_coeff_t coeff = p.arr[0].p.coeff;
        PolyDestroy(&p);
        return PolyFromCoeff(coeff);
    }

    if (PolyHasOnlyPolyZerosAsCoeffsInMonoArray(p)) {
        PolyDestroy(&p);
        return PolyZero();
    }

    return p;
}

/**
 * Mnoży wielomian @p p niebędącego współczynnikiem z wielomianem @p q,
 * który jest współczynnikiem.
 * @param[in] p : wielomian @f$p@f$ niebędący współczynnikiem
 * @param[in] q : wielomian @f$q@f$ będący współczynnikiem
 * @return @f$p * q@f$
 */
Poly PolyMulCoeff(const Poly *p, const Poly *q) {
    Poly product;
    product.size = p->size;
    InitializeMonoArray(&product);

    for (size_t i = 0; i < p->size; ++i) {
        if (PolyIsCoeff(&p->arr[i].p)) {
            product.arr[i] = MonoClone(&p->arr[i]);
            product.arr[i].p.coeff *= q->coeff;

        } else {
            product.arr[i].exp = p->arr[i].exp;
            product.arr[i].p = PolyMul(&p->arr[i].p, q);
        }
    }

    if (PolyHasOnlyPolyZerosAsCoeffsInMonoArray(product)) {
        PolyDestroy(&product);
        return PolyZero();
    }

    return product;
}

/**
 * Mnoży dwa wielomiany.
 * @param[in] p : wielomian @f$p@f$
 * @param[in] q : wielomian @f$q@f$
 * @return @f$p * q@f$
 */
Poly PolyMul(const Poly *p, const Poly *q) {
    assert(p != NULL);
    assert(q != NULL);

    /* Jeśli któryś z wielomianów p i q jest wielomianem tożsamościowo
     * równym zeru, to zwracamy wielomian tożsamościowo równy zeru. */
    if (PolyIsZero(p) || PolyIsZero(q)) {
        return PolyZero();
    }

    if (PolyIsCoeff(p) && PolyIsCoeff(q)) {
        return PolyFromCoeff(p->coeff * q->coeff);
    }

    if (PolyIsCoeff(q)) {
        return PolyMulCoeff(p, q);
    }
    if (PolyIsCoeff(p)) {
        return PolyMulCoeff(q, p);
    }

    /* Tworzymy tablicę jednomianów, do której będziemy wstawiać
     * wszystkie jednomiany, jakie powstaną w wyniku mnożenia
     * każdego jednomianu z tablicy jednomianów wielomianu p
     * z każdym jednomianem z tablicy jednomianów wielomianu q. */
    Mono *monos = malloc((p->size * q->size) * sizeof (Mono));
    CHECK_PTR(monos);
    size_t index = 0;
    for (size_t i = 0; i < p->size; ++i) {
        for (size_t j = 0; j < q->size; ++j) {
            monos[index + j].exp = p->arr[i].exp + q->arr[j].exp;
            monos[index + j].p = PolyMul(&p->arr[i].p, &q->arr[j].p);
        }
        index += q->size;
    }

    /* Z tak powstałej tablicy jednomianów tworzymy wielomian. */
    Poly product = PolyAddMonos(p->size * q->size, monos);
    free(monos);

    if (PolyHasMonoArrayOfSizeZero(product)) {
        PolyDestroy(&product);
        return PolyZero();
    }

    if (PolyHasOnlyPolyZerosAsCoeffsInMonoArray(product)) {
        poly_coeff_t coeff = product.arr[0].p.coeff;
        PolyDestroy(&product);
        return PolyFromCoeff(coeff);
    }

    if (PolyHasOnlyPolyZerosAsCoeffsInMonoArray(product)) {
        PolyDestroy(&product);
        return PolyZero();
    }

    return product;
}

/**
 * Zwraca przeciwny wielomian.
 * @param[in] p : wielomian @f$p@f$
 * @return @f$-p@f$
 */
Poly PolyNeg(const Poly *p) {
    assert(p != NULL);
    /* Przeciwny wielomian to tak naprawdę wielomian p
     * pomnożony przez wielomian stały o współczynniku -1. */
    Poly helper = PolyFromCoeff(-1);
    return PolyMul(p, &helper);
}

/**
 * Odejmuje wielomian od wielomianu.
 * @param[in] p : wielomian @f$p@f$
 * @param[in] q : wielomian @f$q@f$
 * @return @f$p - q@f$
 */
Poly PolySub(const Poly *p, const Poly *q) {
    /* Odejmowanie wielomianu q od wielomianu p to
     * tak naprawdę dodanie do wielomianu p
     * przeciwnego wielomianu q. */
    Poly q_neg = PolyNeg(q);
    Poly difference = PolyAdd(p, &q_neg);
    PolyDestroy(&q_neg);
    return difference;
}

/**
 * Zwraca wykładnik o większej wartości z dwóch podanych wykładników
 * @param[in] a : wykładnik
 * @param[in] b : wykładnik
 * @return wykładnik o większej wartości
 */
static poly_exp_t max(poly_exp_t a, poly_exp_t b) {
    if (a > b) {
        return a;
    }
    return b;
}

/**
 * Zwraca stopień wielomianu ze względu na zadaną zmienną (-1 dla wielomianu
 * tożsamościowo równego zeru). Zmienne indeksowane są od 0.
 * Zmienna o indeksie 0 oznacza zmienną główną tego wielomianu.
 * Większe indeksy oznaczają zmienne wielomianów znajdujących się
 * we współczynnikach.
 * @param[in] p : wielomian
 * @param[in] var_idx : indeks zmiennej
 * @return stopień wielomianu @p p z względu na zmienną o indeksie @p var_idx
 */
poly_exp_t PolyDegBy(const Poly *p, size_t var_idx) {
    assert(p != NULL);

    if (PolyIsZero(p)) {
        return -1;
    }

    if (PolyIsCoeff(p)) {
        /* Wielomian stały ma stopień równy zeru. */
        return 0;
    }

    if (var_idx == 0) {
        /* Jeśli indeks zmiennej to zero, wystarczy zwrócić
         * wykładnik o największej wartości występujący jako wykładnik
         * jednomianu w tablicy jednomianów wielomianu p. */
        return (p->arr[p->size - 1].exp);
    }

    poly_exp_t max_deg = 0; // Największy stopień.
    poly_exp_t curr_deg; // Stopień obecnego wielomianu
                        // (współczynnika jednomianu w tablicy jednomianów).

    for (size_t i = 0; i < p->size; ++i) {
        /* "Zagłębiamy się" o jeden stopień w dany wielomian
         * (współczynnik jednomianu w tablicy jednomianów),
         * a więc wywołujemy funkcję z indeksem zmiennej
         * o jeden mniejszym. */
        curr_deg = PolyDegBy(&p->arr[i].p, var_idx - 1);
        max_deg = max(max_deg, curr_deg);
    }

    return max_deg;
}

/**
 * Zwraca stopień wielomianu (-1 dla wielomianu tożsamościowo równego zeru).
 * @param[in] p : wielomian
 * @return stopień wielomianu @p p
 */
poly_exp_t PolyDeg(const Poly *p) {
    assert(p != NULL);

    if (PolyIsZero(p)) {
        return -1;
    }

    if (PolyIsCoeff(p)) {
        /* Wielomian stały ma stopień równy zeru. */
        return 0;
    }

    poly_exp_t max_deg = 0; // Największy stopień.
    poly_exp_t curr_deg; // Stopień obecnego jednomianu.

    for (size_t i = 0; i < p->size; ++i) {
        /* Stopień obecnego jednomianu (współczynnika
         * jednomianu w tablicy jednomianów) to iloczyn
         * jego wykładnika i stopnia jego współczynnika. */
        curr_deg = p->arr[i].exp + PolyDeg(&p->arr[i].p);
        max_deg = max(max_deg, curr_deg);
    }

    return max_deg;
}

/**
 * Sprawdza równość dwóch wielomianów.
 * @param[in] p : wielomian @f$p@f$
 * @param[in] q : wielomian @f$q@f$
 * @return @f$p = q@f$
 */
bool PolyIsEq(const Poly *p, const Poly *q) {
    assert(p != NULL);
    assert(q != NULL);

    if (PolyIsCoeff(p)) {
        if (PolyIsCoeff(q) && p->coeff == q->coeff) {
            return true;
        } else {
            return false;
        }
    } else {
        if (PolyIsCoeff(q)) {
            return false;
        } else {
            if (p->size != q->size) {
                return false;
            }
            for (size_t i = 0; i < p->size; ++i) {
                if (p->arr[i].exp != q->arr[i].exp) {
                    return false;
                }
                if (!PolyIsEq(&p->arr[i].p, &q->arr[i].p)) {
                    return false;
                }
            }
            return true;
        }
    }
}

/**
 * Wykonuje algorytm szybkiego potęgowania.
 * @param[in] x : podstawa potęgi
 * @param[in] n : wykładnik potęgi
 * @return @f$x^n@f$.
 */
poly_coeff_t FastExponentiation(poly_coeff_t x, poly_coeff_t n) {
    poly_coeff_t res = 1;
    while (n > 0) {
        if (n % 2 == 1) {
            res *= x;
        }
        x *= x;
        n /= 2;
    }
    return res;
}

/**
 * Wylicza wartość wielomianu w punkcie @p x.
 * Wstawia pod pierwszą zmienną wielomianu wartość @p x.
 * W wyniku może powstać wielomian, jeśli współczynniki są wielomianami.
 * Wtedy zmniejszane są o jeden indeksy zmiennych w takim wielomianie.
 * Formalnie dla wielomianu @f$p(x_0, x_1, x_2, \ldots)@f$ wynikiem jest
 * wielomian @f$p(x, x_0, x_1, \ldots)@f$.
 * @param[in] p : wielomian @f$p@f$
 * @param[in] x : wartość argumentu @f$x@f$
 * @return @f$p(x, x_0, x_1, \ldots)@f$
 */
Poly PolyAt(const Poly *p, poly_coeff_t x) {
    assert(p != NULL);

    if (PolyIsCoeff(p)) {
        /* Wartość wielomianu stałego jest taka sama
         * dla dowolnego punktu. */
        return PolyClone(p);
    }

    Poly res = PolyZero();
    for (size_t i = 0; i < p->size; ++i) {
        /* Tworzymy wielomian stały o współczynniku x do potęgi
         * wykładnik obecnego jednomianu. */
        Poly x_raised_to_exp = PolyFromCoeff(FastExponentiation(x,p->arr[i].exp));
        /* Mnożymy ten wielomian przez współczynnik
         * obecnego jednomianu. */
        Poly current = PolyMul(&p->arr[i].p, &x_raised_to_exp);
        /* Aktualizujemy wartość res - dodajemy do wielomianu
         * res wielomian current. */
        Poly new_res = PolyAdd(&res, &current);
        PolyDestroy(&current);
        PolyDestroy(&res);
        res = PolyClone(&new_res);
        PolyDestroy(&new_res);
    }
    return res;
}

/**
 * Sprawdza, czy @p count wynosi zero lub czy tablica @p monos jest pusta.
 * @param[in] count : liczba jednomianów
 * @param[in] monos : tablica jednomianów
 * @return Czy @p count wynosi zero lub tablica @p monos jest pusta?
 */
static bool CountIsZeroOrMonosIsNull(size_t count, const Mono monos[]) {
    return count == 0 || monos == NULL;
}

/**
 * Sumuje listę jednomianów i tworzy z nich wielomian. Przejmuje na własność
 * pamięć wskazywaną przez @p monos i jej zawartość. Może dowolnie modyfikować
 * zawartość tej pamięci. Zakładamy, że pamięć wskazywana przez @p monos
 * została zaalokowana na stercie. Jeśli @p count lub @p monos jest równe zeru
 * (NULL), tworzy wielomian tożsamościowo równy zeru.
 * @param[in] count : liczba jednomianów
 * @param[in] monos : tablica jednomianów
 * @return wielomian będący sumą jednomianów
 */
Poly PolyOwnMonos(size_t count, Mono *monos) {
    if (CountIsZeroOrMonosIsNull(count, monos)) {
        return PolyZero();
    }
    Poly p = PolyAddMonos(count, monos);
    free(monos);
    return p;
}

/**
 * Sumuje listę jednomianów i tworzy z nich wielomian. Nie modyfikuje zawartości
 * tablicy @p monos. Jeśli jest to wymagane, to wykonuje pełne kopie jednomianów
 * z tablicy @p monos. Jeśli @p count lub @p monos jest równe zeru (NULL),
 * tworzy wielomian tożsamościowo równy zeru.
 * @param[in] count : liczba jednomianów
 * @param[in] monos : tablica jednomianów
 * @return wielomian będący sumą jednomianów
 */
Poly PolyCloneMonos(size_t count, const Mono monos[]) {
    if (CountIsZeroOrMonosIsNull(count, monos)) {
        return PolyZero();
    }
    Mono *monos_copy = malloc(count * sizeof (Mono));
    CHECK_PTR(monos_copy);
    for (size_t i = 0; i < count; ++i) {
        monos_copy[i] = MonoClone(&monos[i]);
    }
    Poly p = PolyOwnMonos(count, monos_copy);
    return p;
}

/**
 * Wykonuje algorytm szybkiego potęgowania na wielomianiem @p p.
 * @param[in] p : wielomian będący podstawą potęgi
 * @param[in] n : wykładnik potęgi
 * @return @f$p^n@f$.
 */
static Poly PolyFastExponentiation(const Poly p, poly_exp_t n) {
    if (PolyIsZero(&p)) {
        if (n == 0) {
            /* 0^n == 1, jeśli n == 0. */
            return PolyFromCoeff(1);
        } else {
            /* 0^n == 0, jeśli n != 0. */
            return PolyZero();
        }
    }
    if (n == 1) {
        return PolyClone(&p);
    }
    Poly res = PolyFromCoeff(1);
    Poly p_copy = PolyClone(&p);
    while (n > 0) {
        if (n % 2 == 1) {
            Poly new_res = PolyMul(&res, &p_copy);
            PolyDestroy(&res);
            res = PolyClone(&new_res);
            PolyDestroy(&new_res);
        }
        Poly new_p_copy = PolyMul(&p_copy, &p_copy);
        PolyDestroy(&p_copy);
        p_copy = PolyClone(&new_p_copy);
        PolyDestroy(&new_p_copy);
        n /= 2;
    }
    PolyDestroy(&p_copy);
    return res;
}

/**
 * Sprawdza, czy wielomian @p p powinien zostać "oczyszczony", czyli
 * czy znajdują się w nim jednomiany, których współczynnik jest wielomianem
 * zerowym.
 * @param[in] p : wielomian
 * @return Czy wielomian @p p powinien zostać "oczyszczony" z jednomianów,
 * których współczynnik jest wielomianem zerowym?
 */
static bool PolyNeedsToBeCleaned(const Poly p) {
    if (PolyIsCoeff(&p) && !PolyIsZero(&p)) {
        return false;
    } else {
        for (size_t i = 0; i < p.size; ++i) {
            if (PolyIsZero(&p.arr[i].p)) {
                return true;
            }
            if (PolyNeedsToBeCleaned(p.arr[i].p)) {
                return true;
            }
        }
        return false;
    }
}

/**
 * "Oczyszcza" wielomian @p p z jednomianów, których współczynnik jest wielomianem
 * zerowym.
 * @param[in] p : wielomian
 * @return wielomian @p p bez jednomianów, których współczynnik jest wielomianem
 * zerowym
 */
static Poly PolyClean(const Poly p) {
    if (PolyIsCoeff(&p)) {
        return PolyClone(&p);
    } else {
        Poly res;
        res.arr = malloc(INITIAL_ARRAY_SIZE * sizeof(Mono));
        res.size = INITIAL_ARRAY_SIZE;
        size_t index = 0;
        for (size_t i = 0; i < p.size; ++i) {
            Poly helper = PolyClean(p.arr[i].p);
            PolyAddMono(&res, &index, helper, p.arr[i].exp);
            PolyDestroy(&helper);
        }
        res.size = index;
        return res;
    }
}

/**
 * Składa wielomian @p p z wielomianem @p q.
 * Podstawia w wielomianie @p p pod zmienną @f$x_{0}@f$. wielomian @p q.
 * Jeśli liczba zmiennych wielomianu @p p wynosi @p l i jest większa od
 * 1, pod zmienne @f$x_1,...,x_{l-1}@f$ podstawia zera.
 * @param[in] p : wielomian, którego zmienna @f$x_{0}@f$ zostanie zastąpiona
 * wielomianem @p q[depth]
 * @param[in] q : wielomian, który zostanie podstawiony pod zmienną @f$x_{0}@f$
 * @return @f$p(q,0,0,0,...)@f$
 */
static Poly PolyComposeLastVariable(const Poly *p, const Poly q) {
    Poly sum = PolyZero();
    for (size_t i = 0; i < p->size; ++i) {
        /* Ignorujemy jednomiany, których współczynniki są wielomianami zerowymi. */
        if (!PolyIsZero(&p->arr[i].p)) {
            Poly current = PolyZero(); // Obecny wielomian.
            if (PolyIsCoeff(&p->arr[i].p)) {
                if (p->arr[i].exp == 0) {
                    /* Jeśli współczynnik danego jednomianu jest wielomianem stałym,
                     * a jego wykładnik wynosi zero, obecny wielomian będzie kopią
                     * tego wielomianu stałego. */
                    current = PolyClone(&p->arr[i].p);
                } else {
                    /* Jeśli współczynnik danego jednomianu jest wielomianem stałym,
                     * a jego wykładnik nie wynosi zero, należy podnieść wielomian
                     * q do potęgi równej temu wykładnikowi, a następnie pomnożyć
                     * go przez dany wielomian stały. */
                    current = PolyFastExponentiation(q, p->arr[i].exp);
                    Poly coeff = PolyFromCoeff(p->arr[i].p.coeff);
                    Poly new_current = PolyMul(&current, &coeff);
                    PolyDestroy(&current);
                    PolyDestroy(&coeff);
                    current = PolyClone(&new_current);
                    PolyDestroy(&new_current);
                }
            } else {
                /* Jeśli współczynnik danego jednomianu nie jest wielomianem stałym,
                 * należy obliczyć wartość tego wielomianu, podstawiając pod wszystkie
                 * zmienne zero, czyli tak długo, aż uzyskamy wielomian stały. */
                Poly coeff = PolyAt(&p->arr[i].p, 0);
                while (!PolyIsCoeff(&coeff)) {
                    Poly new_coeff = PolyAt(&coeff, 0);
                    PolyDestroy(&coeff);
                    coeff = PolyClone(&new_coeff);
                    PolyDestroy(&new_coeff);
                }
                /* Jeśli otrzymany wielomian stały jest wielomianem zerowym,
                 * ignorujemy go. */
                if (!PolyIsZero(&coeff)) {
                    if (p->arr[i].exp == 0) {
                        /* Jeśli wykładnik "nowego" współczynnik danego jednomianu
                         * wynosi zero, obecny wielomian będzie kopią nowego
                         * współczynnika. */
                        current = PolyClone(&coeff);
                    } else {
                        /* Jeśli wykładnik "nowego" współczynnik danego jednomianu
                         * nie wynosi zero, należy podnieść wielomian
                         * q do potęgi równej temu wykładnikowi, a następnie pomnożyć
                         * go przez nowy współczynnik. */
                        current = PolyFastExponentiation(q, p->arr[i].exp);
                        Poly new_current = PolyMul(&current, &coeff);
                        PolyDestroy(&current);
                        current = PolyClone(&new_current);
                        PolyDestroy(&new_current);
                    }
                }
                PolyDestroy(&coeff);
            }
            /* Jeśli otrzymany wielomian jest wielomianem zerowym, ignorujemy go. */
            if (!PolyIsZero(&current)) {
                Poly new_sum = PolyAdd(&sum, &current);
                PolyDestroy(&sum);
                sum = PolyClone(&new_sum);
                PolyDestroy(&new_sum);
            }
            PolyDestroy(&current);
        }
    }
    if (PolyIsCoeff(&sum)) {
        return sum;
    }
    if (PolyHasOnlyOneMonoWithNumberAsCoeff(sum)) {
        poly_coeff_t sum_coeff = sum.arr[0].p.coeff;
        PolyDestroy(&sum);
        return PolyFromCoeff(sum_coeff);
    }
    if (PolyHasOnlyPolyZerosAsCoeffsInMonoArray(sum)) {
        PolyDestroy(&sum);
        return PolyZero();
    }
    return sum;
}

/**
 * Powiększa dwuktronie obszar pamięci zarezerwowany dla tablicy jednomianów w wielomianie.
 * Powiększa rozmiar tablicy jednomianów wielomianu @p p o @p additional_size,
 * a następnie zwiększa obszar pamięci tablicy jednomianów.
 * @param[in] p : wielomian
 * @param[in] additional_size : rozmiar, o jaki zostanie powiększony rozmiar
 * tablicy jednomianów wielomianu
 */
static void ExpandMonoArray(Poly *p, size_t additional_size) {
    p->size = p->size + additional_size;
    p->arr = realloc(p->arr, p->size * sizeof(Mono));
    CHECK_PTR(p->arr);
}

/**
 * Składa wielomian @p p z wielomianem w tablicy @p q[].
 * Funkcja pomocnicza funkcji PolyCompose.
 * Podstawia w wielomianie @p p pod zmienną @f$x_{0}@f$. wielomian @p q[depth].
 * Jeśli liczba zmiennych wielomianu @p p wynosi @p l i jest większa od
 * @p k, pod zmienne @f$x_{k},...,x_{l-1}@f$ podstawia zera.
 * Jeśli @p depth + 1 != @p k, najpierw podstawia pod zmienne @f$x_{i}@f$
 * wielomiany @p q[depth+i] dla @f$i=1,...,k-depth-1@f$.
 * @param[in] p : wielomian, którego zmienna @f$x_{0}@f$ zostanie zastąpiona
 * wielomianem @p q[depth]
 * @param[in] k : rozmiar tablicy wielomianów @p q[]
 * @param[in] q : tablica wielomianów
 * @param[in] depth : indeks wielomianu w tablicy @p q[], który zostanie
 * podstawiony pod zmienną @f$x_{0}@f$ w wielomianie @p p
 * @return @f$p(q[depth],q[depth+1],q[depth+2],..,q[k-1],0,0,0,...)@f$
 */
static Poly PolyComposeHelper(const Poly *p, size_t k, const Poly q[], size_t depth) {
    if (PolyIsCoeff(p)) {
        return PolyFromCoeff(p->coeff);
    }
    if (depth + 1 == k) {
        return PolyComposeLastVariable(p, q[depth]);
    }
    Poly sum = PolyZero();
    Poly coeff;
    for (size_t i = 0; i < p->size; ++i) {
        /* Znajdujemy wielomian będący złożeniem współczynnika danego jednomianu
         * z odpowiednimi wielomianami z tablicy q. */
        coeff = PolyComposeHelper(&p->arr[i].p, k, q, depth + 1);
        /* Jeśli otrzymany wielomian jest wielomianem zerowym, ignorujemy go. */
        if (!PolyIsZero(&coeff)) {
            Poly current;
            if (p->arr[i].exp != 0) {
                current.size = 0;
                current.arr = malloc(sizeof(Mono));
                CHECK_PTR(current.arr);
                /* Należy podnieść wielomian q[depth] do potęgi równej wykładnikowi danego jednomianu. */
                Poly helper = PolyFastExponentiation(q[depth], p->arr[i].exp);
                /* Jeśli wielomian helper jest wielomianem zerowym, ignorujemy go. */
                if (!PolyIsZero(&helper)) {
                    if (PolyIsCoeff(&coeff)) {
                        /* Wielomian coeff jest wielomianem stałym. */
                        if (PolyIsCoeff(&helper)) {
                            /* Jeśli wielomian helper jest wielomianem stałym, należy
                             * dodać do tablicy jednomianów wielomianu current wielomian
                             * coeff * helper z wykładnikiem 0. */
                            ExpandMonoArray(&current, 1);
                            current.arr[0].p = PolyMul(&coeff, &helper);
                            current.arr[0].exp = 0;
                        } else {
                            /* Jeśli wielomian helper nie jest wielomianem stałym, należy
                             * dodać do tablicy jednomianów tyle jednomianów, ile znajduje się
                             * w tablicy jednomianów wielomianu helper. Każdy taki jednomian
                             * składa się z wielomianu coeff pomnożonego przez współczynnik
                             * kolejnego jednomianu w tablicy jednomianów wielomianu helper
                             * oraz wykładnika równego wykładnikowi danego jednomianu. */
                            ExpandMonoArray(&current, helper.size);
                            for (size_t j = 0; j < helper.size; ++j) {
                                current.arr[j].p = PolyMul(&coeff, &helper.arr[j].p);
                                current.arr[j].exp = helper.arr[j].exp;
                            }
                        }
                    } else {
                        /* Jeśli wielomian coeff nie jest wielomianem stałym, należy do tablicy jednomianów
                         * wielomianu current dodać wszystkie możliwe jednomiany w tablicy jednomianów
                         * wielomianu coeff pomnożone przez wszystkie możliwe jednomiany w tablicy
                         * jednomianów wielomianu helper (lub tylko przez niego, jeśli jest
                         * wielomianem stałym), ignorując wielomiany zerowe. */
                        size_t index = 0;
                        for (size_t j = 0; j < coeff.size; ++j) {
                            if (!PolyIsZero(&coeff.arr[j].p)) {
                                if (PolyIsCoeff(&helper)) {
                                    /* Jeśli wielomian helper jest wielomianem stałym, należy
                                     * dodać do tablicy jednomianów wielomianu current wielomian
                                     * helper pomnożony przez obecny jednomian w tablicy jednomianów
                                     * wielomianu coeff z wykładnikiem równym wykładnikowi danego
                                     * jednomianu. */
                                    ExpandMonoArray(&current, 1);
                                    current.arr[index].p = PolyMul(&coeff.arr[j].p, &helper);
                                    current.arr[index].exp = coeff.arr[j].exp;
                                    index++;
                                } else {
                                    /* Jeśli wielomian helper nie jest wielomianem stałym, należy
                                     * dodać do tablicy jednomianów tyle jednomianów, ile znajduje się
                                     * w tablicy jednomianów wielomianu helper. Każdy taki jednomian
                                     * składa się z współczynnika danego jednomianu w tablicy jednomianów
                                     * wielomianu coeff pomnożonego przez współczynnik kolejnego jednomianu
                                     * w tablicy jednomianów wielomianu helper oraz wykładnika równego
                                     * sumie wykładników tych jednomianów. */
                                    ExpandMonoArray(&current, helper.size);
                                    for (size_t l = 0; l < helper.size; ++l) {
                                        current.arr[index + l].p = PolyMul(&coeff.arr[j].p, &helper.arr[l].p);
                                        current.arr[index + l].exp = coeff.arr[j].exp + helper.arr[l].exp;
                                    }
                                    index += helper.size;
                                }
                            }
                        }
                    }
                }
                PolyDestroy(&helper);
            } else {
                /* Jeśli wykładnik danego jednomianu wynosi zero, wystarczy
                 * skopiować wielomian coeff. */
                current = PolyClone(&coeff);
            }
            /* Jeśli wielomian current nie jest wielomianem stałym, a rozmiar jego tablicy
             * jednomianów wynosi zero, oznacza to, że żaden jednomian nie został dodany
             * do jego tablicy jednomianów, więc należy go zignorować. */
            if (!PolyIsZero(&current) && !(!PolyIsCoeff(&current) && current.size == 0)) {
                Poly new_sum = PolyAdd(&sum, &current);
                PolyDestroy(&sum);
                sum = PolyClone(&new_sum);
                PolyDestroy(&new_sum);
            }
            PolyDestroy(&current);
        }
        PolyDestroy(&coeff);
    }
    if (PolyIsCoeff(&sum)) {
        return sum;
    }
    if (PolyHasOnlyOneMonoWithNumberAsCoeff(sum)) {
        poly_coeff_t sum_coeff = sum.arr[0].p.coeff;
        PolyDestroy(&sum);
        return PolyFromCoeff(sum_coeff);
    }
    if (PolyHasOnlyPolyZerosAsCoeffsInMonoArray(sum)) {
        PolyDestroy(&sum);
        return PolyZero();
    }
    return sum;
}

/**
 * Składa wielomian @p p z wielomianami w tablicy @p q[].
 * Niech l oznacza liczbę zmiennych wielomianu p i niech te zmienne są
 * oznaczone odpowiednio @f$x_0,x_1,x_2,...,x_{l-1}@f$.
 * Podstawia w wielomianie @p p pod zmienną @f$x_{i}@f$. wielomian @p q[i]
 * dla @f$i=0,...,min(k,l)-1@f$.
 * Jeśli @f$k<l@f$, to pod zmienne @f$x_k,...,x_{l-1}@f$ podstawiamy zera.
 * @param[in] p : wielomian, którego zmienne zostaną zastąpione wielomianami
 * z tablicy @p q[] oraz ewentualnie zerami
 * @param[in] k : rozmiar tablicy wielomianów @p q[]
 * @param[in] q : tablica wielomianów
 * @return @f$p(q[0],q[1],q[2],..,q[k-1],0,0,0,...)@f$
 */
Poly PolyCompose(const Poly *p, size_t k, const Poly q[]) {
    if (k == 0) {
        Poly helper = PolyAt(p, 0);
        while (!PolyIsCoeff(&helper)) {
            Poly new_helper = PolyAt(&helper, 0);
            PolyDestroy(&helper);
            helper = PolyClone(&new_helper);
            PolyDestroy(&new_helper);
        }
        return helper;
    }

    Poly result = PolyComposeHelper(p, k, q, 0);

    if (PolyIsCoeff(&result)) {
        return result;
    }

    if (PolyHasOnlyOneMonoWithNumberAsCoeff(result)) {
        poly_coeff_t coeff = result.arr[0].p.coeff;
        PolyDestroy(&result);
        return PolyFromCoeff(coeff);
    }

    if (PolyHasOnlyPolyZerosAsCoeffsInMonoArray(result)) {
        PolyDestroy(&result);
        return PolyZero();
    }

    if (PolyNeedsToBeCleaned(result)) {
        Poly clean_result = PolyClean(result);
        PolyDestroy(&result);
        return clean_result;
    } else {
        return result;
    }
}