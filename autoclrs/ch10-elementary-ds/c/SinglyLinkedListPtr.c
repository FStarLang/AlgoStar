/*
 * Pointer-based Singly Linked List — C implementation with c2pulse verification.
 *
 * Uses a proper recursive struct node { data, next } with heap allocation.
 * c2pulse generates:
 *   - struct_node type with data/next fields
 *   - struct_node__pred shallow ownership predicate
 *   - Fold/unfold ghost operations
 *   - Field projections (struct_node__get_data, struct_node__get_next)
 *
 * The higher-level list operations (insert, search) are written directly in
 * Pulse in SinglyLinkedListPtr.Helpers.fst, using the recursive is_list predicate
 * and calling the c2pulse-generated struct operations.
 */

#include "c2pulse.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

typedef struct node {
    int data;
    struct node *next;
} node;

/* Simple getter: read data field from a non-null node */
int get_data(node *n)
{
    return n->data;
}

/* Simple setter: write data field on a non-null node */
void set_data(node *n, int x)
{
    n->data = x;
}
