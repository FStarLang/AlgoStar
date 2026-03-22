/*
 * main.c — Test harness for Ch10 elementary data structures.
 *
 * Calls the extracted test functions for Stack, Queue,
 * Singly Linked List, and Doubly Linked List.
 *
 * Build: see Makefile 'test-c' target
 */

#include <stdio.h>

#include "CLRS_Ch10_Stack_ImplTest.h"
#include "CLRS_Ch10_Queue_ImplTest.h"
#include "CLRS_Ch10_SinglyLinkedList_ImplTest.h"
#include "CLRS_Ch10_DLL_ImplTest.h"

int main(void)
{
    printf("Ch10 Elementary Data Structures — Concrete Execution Tests\n");
    printf("==========================================================\n\n");

    printf("  [Stack]  test_stack_spec_validation ... ");
    fflush(stdout);
    CLRS_Ch10_Stack_ImplTest_test_stack_spec_validation();
    printf("PASS\n");

    printf("  [Queue]  test_queue_spec_validation ... ");
    fflush(stdout);
    CLRS_Ch10_Queue_ImplTest_test_queue_spec_validation();
    printf("PASS\n");

    printf("  [SLL]    test_sll_spec_validation   ... ");
    fflush(stdout);
    CLRS_Ch10_SinglyLinkedList_ImplTest_test_sll_spec_validation();
    printf("PASS\n");

    printf("  [DLL]    test_dll_spec_validation   ... ");
    fflush(stdout);
    CLRS_Ch10_DLL_ImplTest_test_dll_spec_validation();
    printf("PASS\n");

    printf("\nAll Ch10 tests passed.\n");
    return 0;
}
