/* krml header omitted for test repeatability */


#include "internal/CLRS_Ch10_SinglyLinkedList_ImplTest.h"

static FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_
list_insert(
  krml_checked_int_t x,
  FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_ head
)
{
  CLRS_Ch10_SinglyLinkedList_Base_node
  *nd = KRML_HOST_MALLOC(sizeof (CLRS_Ch10_SinglyLinkedList_Base_node));
  if (nd != NULL)
    nd[0U] = ((CLRS_Ch10_SinglyLinkedList_Base_node){ .key = x, .next = head });
  return
    (
      (FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_){
        .tag = FStar_Pervasives_Native_Some,
        .v = nd
      }
    );
}

bool
CLRS_Ch10_SinglyLinkedList_Impl_list_search(
  FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_ head,
  krml_checked_int_t k
)
{
  if (head.tag == FStar_Pervasives_Native_None)
    return false;
  else if (head.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_SinglyLinkedList_Base_node *vl = head.v;
    CLRS_Ch10_SinglyLinkedList_Base_node nd = *vl;
    if (nd.key == k)
      return true;
    else
      return CLRS_Ch10_SinglyLinkedList_Impl_list_search(nd.next, k);
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_
CLRS_Ch10_SinglyLinkedList_Impl_list_delete(
  FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_ head,
  krml_checked_int_t k
)
{
  if (head.tag == FStar_Pervasives_Native_None)
    return head;
  else if (head.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_SinglyLinkedList_Base_node *vl = head.v;
    CLRS_Ch10_SinglyLinkedList_Base_node nd = *vl;
    if (nd.key == k)
    {
      FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_ tail = nd.next;
      KRML_HOST_FREE(vl);
      return tail;
    }
    else
    {
      FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_
      new_tail = CLRS_Ch10_SinglyLinkedList_Impl_list_delete(nd.next, k);
      *vl = ((CLRS_Ch10_SinglyLinkedList_Base_node){ .key = nd.key, .next = new_tail });
      return
        (
          (FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_){
            .tag = FStar_Pervasives_Native_Some,
            .v = vl
          }
        );
    }
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool CLRS_Ch10_SinglyLinkedList_ImplTest_bool_eq(bool a, bool b)
{
  return a == b;
}

bool CLRS_Ch10_SinglyLinkedList_ImplTest_test_sll_spec_validation(void)
{
  FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_
  hd = { .tag = FStar_Pervasives_Native_None };
  FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_
  hd1 = list_insert((krml_checked_int_t)3, hd);
  FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_
  hd2 = list_insert((krml_checked_int_t)2, hd1);
  FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_
  hd3 = list_insert((krml_checked_int_t)1, hd2);
  bool found = CLRS_Ch10_SinglyLinkedList_Impl_list_search(hd3, (krml_checked_int_t)2);
  bool pass = found == true;
  bool not_found = CLRS_Ch10_SinglyLinkedList_Impl_list_search(hd3, (krml_checked_int_t)99);
  bool pass1 = pass && not_found == false;
  FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_
  hd4 = CLRS_Ch10_SinglyLinkedList_Impl_list_delete(hd3, (krml_checked_int_t)2);
  FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_
  hd5 = CLRS_Ch10_SinglyLinkedList_Impl_list_delete(hd4, (krml_checked_int_t)99);
  bool gone = CLRS_Ch10_SinglyLinkedList_Impl_list_search(hd5, (krml_checked_int_t)2);
  bool pass2 = pass1 && gone == false;
  bool still1 = CLRS_Ch10_SinglyLinkedList_Impl_list_search(hd5, (krml_checked_int_t)1);
  bool pass3 = pass2 && still1 == true;
  bool still3 = CLRS_Ch10_SinglyLinkedList_Impl_list_search(hd5, (krml_checked_int_t)3);
  bool pass4 = pass3 && still3 == true;
  FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_
  hd6 = CLRS_Ch10_SinglyLinkedList_Impl_list_delete(hd5, (krml_checked_int_t)1);
  FStar_Pervasives_Native_option___CLRS_Ch10_SinglyLinkedList_Base_node_
  hd7 = CLRS_Ch10_SinglyLinkedList_Impl_list_delete(hd6, (krml_checked_int_t)3);
  KRML_MAYBE_UNUSED_VAR(hd7);
  return pass4;
}

