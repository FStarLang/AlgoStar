/* krml header omitted for test repeatability */


#include "internal/CLRS_Ch10_DLL_ImplTest.h"

#include "internal/FStar_Pulse_PulseCore_Prims.h"
#include "internal/CLRS_Ch10_SinglyLinkedList_ImplTest.h"

static void
set_prev(
  CLRS_Ch10_DLL_Impl_node *p,
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ prev_
)
{
  (*p).prev = prev_;
}

static void
list_insert(
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ *hd_ref,
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ *tl_ref,
  krml_checked_int_t x
)
{
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd1 = *hd_ref;
  if (hd1.tag == FStar_Pervasives_Native_None)
  {
    CLRS_Ch10_DLL_Impl_node *nd = KRML_HOST_MALLOC(sizeof (CLRS_Ch10_DLL_Impl_node));
    if (nd != NULL)
      nd[0U] =
        (
          (CLRS_Ch10_DLL_Impl_node){
            .key = x,
            .prev = { .tag = FStar_Pervasives_Native_None },
            .next = { .tag = FStar_Pervasives_Native_None }
          }
        );
    *hd_ref =
      (
        (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .tag = FStar_Pervasives_Native_Some,
          .v = nd
        }
      );
    *tl_ref =
      (
        (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .tag = FStar_Pervasives_Native_Some,
          .v = nd
        }
      );
  }
  else if (hd1.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_DLL_Impl_node *old_hp = hd1.v;
    CLRS_Ch10_DLL_Impl_node *nd = KRML_HOST_MALLOC(sizeof (CLRS_Ch10_DLL_Impl_node));
    if (nd != NULL)
      nd[0U] =
        (
          (CLRS_Ch10_DLL_Impl_node){
            .key = x,
            .prev = { .tag = FStar_Pervasives_Native_None },
            .next = { .tag = FStar_Pervasives_Native_Some, .v = old_hp }
          }
        );
    set_prev(old_hp,
      (
        (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .tag = FStar_Pervasives_Native_Some,
          .v = nd
        }
      ));
    *hd_ref =
      (
        (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .tag = FStar_Pervasives_Native_Some,
          .v = nd
        }
      );
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

static void
list_insert_tail(
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ *hd_ref,
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ *tl_ref,
  krml_checked_int_t x
)
{
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd1 = *hd_ref;
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ tl1 = *tl_ref;
  if (hd1.tag == FStar_Pervasives_Native_None)
  {
    CLRS_Ch10_DLL_Impl_node *nd = KRML_HOST_MALLOC(sizeof (CLRS_Ch10_DLL_Impl_node));
    if (nd != NULL)
      nd[0U] =
        (
          (CLRS_Ch10_DLL_Impl_node){
            .key = x,
            .prev = { .tag = FStar_Pervasives_Native_None },
            .next = { .tag = FStar_Pervasives_Native_None }
          }
        );
    *hd_ref =
      (
        (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .tag = FStar_Pervasives_Native_Some,
          .v = nd
        }
      );
    *tl_ref =
      (
        (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .tag = FStar_Pervasives_Native_Some,
          .v = nd
        }
      );
  }
  else if (hd1.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_DLL_Impl_node *old_hp = hd1.v;
    CLRS_Ch10_DLL_Impl_node *concrete_tp;
    if (tl1.tag == FStar_Pervasives_Native_Some)
      concrete_tp = tl1.v;
    else
      concrete_tp =
        KRML_EABORT(CLRS_Ch10_DLL_Impl_node *,
          "unreachable (pattern matches are exhaustive in F*)");
    CLRS_Ch10_DLL_Impl_node *nd = KRML_HOST_MALLOC(sizeof (CLRS_Ch10_DLL_Impl_node));
    if (nd != NULL)
      nd[0U] =
        (
          (CLRS_Ch10_DLL_Impl_node){
            .key = x,
            .prev = { .tag = FStar_Pervasives_Native_Some, .v = concrete_tp },
            .next = { .tag = FStar_Pervasives_Native_None }
          }
        );
    (*concrete_tp).next =
      (
        (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .tag = FStar_Pervasives_Native_Some,
          .v = nd
        }
      );
    *hd_ref =
      (
        (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .tag = FStar_Pervasives_Native_Some,
          .v = old_hp
        }
      );
    *tl_ref =
      (
        (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .tag = FStar_Pervasives_Native_Some,
          .v = nd
        }
      );
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

bool CLRS_Ch10_DLL_Impl_search_dls(CLRS_Ch10_DLL_Impl_node *p, krml_checked_int_t k)
{
  CLRS_Ch10_DLL_Impl_node nd = *p;
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ nxt = nd.next;
  if (nd.key == k)
    return true;
  else if (nxt.tag == FStar_Pervasives_Native_None)
    return false;
  else if (nxt.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_DLL_Impl_node *np = nxt.v;
    return CLRS_Ch10_DLL_Impl_search_dls(np, k);
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

static bool
list_search(FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd, krml_checked_int_t k)
{
  if (hd.tag == FStar_Pervasives_Native_None)
    return false;
  else if (hd.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_DLL_Impl_node *hp = hd.v;
    return CLRS_Ch10_DLL_Impl_search_dls(hp, k);
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

FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
CLRS_Ch10_DLL_Impl_search_dls_ptr(CLRS_Ch10_DLL_Impl_node *p, krml_checked_int_t k)
{
  CLRS_Ch10_DLL_Impl_node nd = *p;
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ nxt = nd.next;
  if (nd.key == k)
    return
      (
        (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .tag = FStar_Pervasives_Native_Some,
          .v = p
        }
      );
  else if (nxt.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (nxt.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_DLL_Impl_node *np = nxt.v;
    return CLRS_Ch10_DLL_Impl_search_dls_ptr(np, k);
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

static FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
list_search_ptr(
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd,
  krml_checked_int_t k
)
{
  if (hd.tag == FStar_Pervasives_Native_None)
    return
      (
        (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .tag = FStar_Pervasives_Native_None
        }
      );
  else if (hd.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_DLL_Impl_node *hp = hd.v;
    return CLRS_Ch10_DLL_Impl_search_dls_ptr(hp, k);
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

bool CLRS_Ch10_DLL_Impl_search_dls_rev(CLRS_Ch10_DLL_Impl_node *p, krml_checked_int_t k)
{
  CLRS_Ch10_DLL_Impl_node nd = *p;
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ prv = nd.prev;
  if (nd.key == k)
    return true;
  else if (prv.tag == FStar_Pervasives_Native_None)
    return false;
  else if (prv.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_DLL_Impl_node *pp = prv.v;
    return CLRS_Ch10_DLL_Impl_search_dls_rev(pp, k);
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

static bool
list_search_back(
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd,
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ tl,
  krml_checked_int_t k
)
{
  if (hd.tag == FStar_Pervasives_Native_None)
    return false;
  else if (hd.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_DLL_Impl_node *concrete_tp;
    if (tl.tag == FStar_Pervasives_Native_Some)
      concrete_tp = tl.v;
    else
      concrete_tp =
        KRML_EABORT(CLRS_Ch10_DLL_Impl_node *,
          "unreachable (pattern matches are exhaustive in F*)");
    return CLRS_Ch10_DLL_Impl_search_dls_rev(concrete_tp, k);
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

static FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
fst__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(
  K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
  x
)
{
  return x.fst;
}

static FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
snd__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(
  K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
  x
)
{
  return x.snd;
}

K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
CLRS_Ch10_DLL_Impl_delete_in_dls(
  CLRS_Ch10_DLL_Impl_node *p,
  krml_checked_int_t k,
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ prev_ptr,
  CLRS_Ch10_DLL_Impl_node *tail_ptr
)
{
  CLRS_Ch10_DLL_Impl_node nd = *p;
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ nxt = nd.next;
  if (nd.key == k)
    if (nxt.tag == FStar_Pervasives_Native_None)
    {
      KRML_HOST_FREE(p);
      FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
      none_ptr = { .tag = FStar_Pervasives_Native_None };
      return
        (
          (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .fst = none_ptr,
            .snd = none_ptr
          }
        );
    }
    else if (nxt.tag == FStar_Pervasives_Native_Some)
    {
      CLRS_Ch10_DLL_Impl_node *np = nxt.v;
      KRML_HOST_FREE(p);
      set_prev(np, prev_ptr);
      return
        (
          (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .fst = { .tag = FStar_Pervasives_Native_Some, .v = np },
            .snd = { .tag = FStar_Pervasives_Native_Some, .v = tail_ptr }
          }
        );
    }
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  else if (nxt.tag == FStar_Pervasives_Native_None)
    return
      (
        (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .fst = { .tag = FStar_Pervasives_Native_Some, .v = p },
          .snd = { .tag = FStar_Pervasives_Native_Some, .v = tail_ptr }
        }
      );
  else if (nxt.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_DLL_Impl_node *np = nxt.v;
    K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
    r =
      CLRS_Ch10_DLL_Impl_delete_in_dls(np,
        k,
        (
          (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .tag = FStar_Pervasives_Native_Some,
            .v = p
          }
        ),
        tail_ptr);
    FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
    new_hd =
      fst__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(r);
    FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
    new_tl =
      snd__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(r);
    if (new_hd.tag == FStar_Pervasives_Native_None)
    {
      *p =
        (
          (CLRS_Ch10_DLL_Impl_node){
            .key = nd.key,
            .prev = nd.prev,
            .next = { .tag = FStar_Pervasives_Native_None }
          }
        );
      return
        (
          (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .fst = { .tag = FStar_Pervasives_Native_Some, .v = p },
            .snd = { .tag = FStar_Pervasives_Native_Some, .v = p }
          }
        );
    }
    else if (new_hd.tag == FStar_Pervasives_Native_Some)
    {
      CLRS_Ch10_DLL_Impl_node *new_hp = new_hd.v;
      CLRS_Ch10_DLL_Impl_node *concrete_tp;
      if (new_tl.tag == FStar_Pervasives_Native_Some)
        concrete_tp = new_tl.v;
      else
        concrete_tp =
          KRML_EABORT(CLRS_Ch10_DLL_Impl_node *,
            "unreachable (pattern matches are exhaustive in F*)");
      *p =
        (
          (CLRS_Ch10_DLL_Impl_node){
            .key = nd.key,
            .prev = nd.prev,
            .next = { .tag = FStar_Pervasives_Native_Some, .v = new_hp }
          }
        );
      return
        (
          (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .fst = { .tag = FStar_Pervasives_Native_Some, .v = p },
            .snd = { .tag = FStar_Pervasives_Native_Some, .v = concrete_tp }
          }
        );
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
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static void
list_delete(
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ *hd_ref,
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ *tl_ref,
  krml_checked_int_t k
)
{
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd1 = *hd_ref;
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ tl1 = *tl_ref;
  if (hd1.tag == FStar_Pervasives_Native_None)
  {
    *hd_ref = hd1;
    *tl_ref = tl1;
  }
  else if (hd1.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_DLL_Impl_node *hp = hd1.v;
    CLRS_Ch10_DLL_Impl_node *concrete_tp;
    if (tl1.tag == FStar_Pervasives_Native_Some)
      concrete_tp = tl1.v;
    else
      concrete_tp =
        KRML_EABORT(CLRS_Ch10_DLL_Impl_node *,
          "unreachable (pattern matches are exhaustive in F*)");
    K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
    r =
      CLRS_Ch10_DLL_Impl_delete_in_dls(hp,
        k,
        (
          (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .tag = FStar_Pervasives_Native_None
          }
        ),
        concrete_tp);
    FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
    new_hd =
      fst__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(r);
    FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
    new_tl =
      snd__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(r);
    *hd_ref = new_hd;
    *tl_ref = new_tl;
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

K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
CLRS_Ch10_DLL_Impl_delete_at_in_dls(
  CLRS_Ch10_DLL_Impl_node *p,
  krml_checked_int_t i,
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ prev_ptr,
  CLRS_Ch10_DLL_Impl_node *tail_ptr
)
{
  CLRS_Ch10_DLL_Impl_node nd = *p;
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ nxt = nd.next;
  if (i == (krml_checked_int_t)0)
    if (nxt.tag == FStar_Pervasives_Native_None)
    {
      KRML_HOST_FREE(p);
      FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
      none_ptr = { .tag = FStar_Pervasives_Native_None };
      return
        (
          (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .fst = none_ptr,
            .snd = none_ptr
          }
        );
    }
    else if (nxt.tag == FStar_Pervasives_Native_Some)
    {
      CLRS_Ch10_DLL_Impl_node *np = nxt.v;
      KRML_HOST_FREE(p);
      set_prev(np, prev_ptr);
      return
        (
          (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .fst = { .tag = FStar_Pervasives_Native_Some, .v = np },
            .snd = { .tag = FStar_Pervasives_Native_Some, .v = tail_ptr }
          }
        );
    }
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  else if (nxt.tag == FStar_Pervasives_Native_None)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (nxt.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_DLL_Impl_node *np = nxt.v;
    K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
    r =
      CLRS_Ch10_DLL_Impl_delete_at_in_dls(np,
        Prims_op_Subtraction(i, (krml_checked_int_t)1),
        (
          (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .tag = FStar_Pervasives_Native_Some,
            .v = p
          }
        ),
        tail_ptr);
    FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
    new_hd =
      fst__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(r);
    FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
    new_tl =
      snd__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(r);
    if (new_hd.tag == FStar_Pervasives_Native_None)
    {
      *p =
        (
          (CLRS_Ch10_DLL_Impl_node){
            .key = nd.key,
            .prev = nd.prev,
            .next = { .tag = FStar_Pervasives_Native_None }
          }
        );
      return
        (
          (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .fst = { .tag = FStar_Pervasives_Native_Some, .v = p },
            .snd = { .tag = FStar_Pervasives_Native_Some, .v = p }
          }
        );
    }
    else if (new_hd.tag == FStar_Pervasives_Native_Some)
    {
      CLRS_Ch10_DLL_Impl_node *new_hp = new_hd.v;
      CLRS_Ch10_DLL_Impl_node *concrete_tp;
      if (new_tl.tag == FStar_Pervasives_Native_Some)
        concrete_tp = new_tl.v;
      else
        concrete_tp =
          KRML_EABORT(CLRS_Ch10_DLL_Impl_node *,
            "unreachable (pattern matches are exhaustive in F*)");
      *p =
        (
          (CLRS_Ch10_DLL_Impl_node){
            .key = nd.key,
            .prev = nd.prev,
            .next = { .tag = FStar_Pervasives_Native_Some, .v = new_hp }
          }
        );
      return
        (
          (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .fst = { .tag = FStar_Pervasives_Native_Some, .v = p },
            .snd = { .tag = FStar_Pervasives_Native_Some, .v = concrete_tp }
          }
        );
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
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static void
list_delete_node(
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ *hd_ref,
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ *tl_ref,
  krml_checked_int_t i
)
{
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd1 = *hd_ref;
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ tl1 = *tl_ref;
  CLRS_Ch10_DLL_Impl_node *concrete_hp;
  if (hd1.tag == FStar_Pervasives_Native_Some)
    concrete_hp = hd1.v;
  else
    concrete_hp =
      KRML_EABORT(CLRS_Ch10_DLL_Impl_node *,
        "unreachable (pattern matches are exhaustive in F*)");
  CLRS_Ch10_DLL_Impl_node *concrete_tp;
  if (tl1.tag == FStar_Pervasives_Native_Some)
    concrete_tp = tl1.v;
  else
    concrete_tp =
      KRML_EABORT(CLRS_Ch10_DLL_Impl_node *,
        "unreachable (pattern matches are exhaustive in F*)");
  K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
  r =
    CLRS_Ch10_DLL_Impl_delete_at_in_dls(concrete_hp,
      i,
      (
        (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
          .tag = FStar_Pervasives_Native_None
        }
      ),
      concrete_tp);
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
  new_hd =
    fst__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(r);
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
  new_tl =
    snd__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(r);
  *hd_ref = new_hd;
  *tl_ref = new_tl;
}

K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
CLRS_Ch10_DLL_Impl_delete_last_in_dls(
  CLRS_Ch10_DLL_Impl_node *p,
  krml_checked_int_t k,
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ prev_ptr,
  CLRS_Ch10_DLL_Impl_node *tail_ptr
)
{
  CLRS_Ch10_DLL_Impl_node nd = *p;
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ nxt = nd.next;
  if (nxt.tag == FStar_Pervasives_Native_None)
    if (nd.key == k)
    {
      KRML_HOST_FREE(p);
      FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
      none_ptr = { .tag = FStar_Pervasives_Native_None };
      return
        (
          (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .fst = none_ptr,
            .snd = none_ptr
          }
        );
    }
    else
      return
        (
          (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .fst = { .tag = FStar_Pervasives_Native_Some, .v = p },
            .snd = { .tag = FStar_Pervasives_Native_Some, .v = tail_ptr }
          }
        );
  else if (nxt.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_DLL_Impl_node *np = nxt.v;
    bool in_tail = CLRS_Ch10_DLL_Impl_search_dls(np, k);
    if (in_tail)
    {
      K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
      r =
        CLRS_Ch10_DLL_Impl_delete_last_in_dls(np,
          k,
          (
            (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
              .tag = FStar_Pervasives_Native_Some,
              .v = p
            }
          ),
          tail_ptr);
      FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
      new_hd =
        fst__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(r);
      FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
      new_tl =
        snd__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(r);
      if (new_hd.tag == FStar_Pervasives_Native_None)
      {
        *p =
          (
            (CLRS_Ch10_DLL_Impl_node){
              .key = nd.key,
              .prev = nd.prev,
              .next = { .tag = FStar_Pervasives_Native_None }
            }
          );
        return
          (
            (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
              .fst = { .tag = FStar_Pervasives_Native_Some, .v = p },
              .snd = { .tag = FStar_Pervasives_Native_Some, .v = p }
            }
          );
      }
      else if (new_hd.tag == FStar_Pervasives_Native_Some)
      {
        CLRS_Ch10_DLL_Impl_node *new_hp = new_hd.v;
        CLRS_Ch10_DLL_Impl_node *concrete_tp;
        if (new_tl.tag == FStar_Pervasives_Native_Some)
          concrete_tp = new_tl.v;
        else
          concrete_tp =
            KRML_EABORT(CLRS_Ch10_DLL_Impl_node *,
              "unreachable (pattern matches are exhaustive in F*)");
        *p =
          (
            (CLRS_Ch10_DLL_Impl_node){
              .key = nd.key,
              .prev = nd.prev,
              .next = { .tag = FStar_Pervasives_Native_Some, .v = new_hp }
            }
          );
        return
          (
            (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
              .fst = { .tag = FStar_Pervasives_Native_Some, .v = p },
              .snd = { .tag = FStar_Pervasives_Native_Some, .v = concrete_tp }
            }
          );
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
    else if (nd.key == k)
    {
      KRML_HOST_FREE(p);
      set_prev(np, prev_ptr);
      return
        (
          (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .fst = { .tag = FStar_Pervasives_Native_Some, .v = np },
            .snd = { .tag = FStar_Pervasives_Native_Some, .v = tail_ptr }
          }
        );
    }
    else
      return
        (
          (K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .fst = { .tag = FStar_Pervasives_Native_Some, .v = p },
            .snd = { .tag = FStar_Pervasives_Native_Some, .v = tail_ptr }
          }
        );
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

static void
list_delete_last(
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ *hd_ref,
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ *tl_ref,
  krml_checked_int_t k
)
{
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd1 = *hd_ref;
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ tl1 = *tl_ref;
  if (hd1.tag == FStar_Pervasives_Native_None)
  {
    *hd_ref = hd1;
    *tl_ref = tl1;
  }
  else if (hd1.tag == FStar_Pervasives_Native_Some)
  {
    CLRS_Ch10_DLL_Impl_node *hp = hd1.v;
    CLRS_Ch10_DLL_Impl_node *concrete_tp;
    if (tl1.tag == FStar_Pervasives_Native_Some)
      concrete_tp = tl1.v;
    else
      concrete_tp =
        KRML_EABORT(CLRS_Ch10_DLL_Impl_node *,
          "unreachable (pattern matches are exhaustive in F*)");
    K___FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
    r =
      CLRS_Ch10_DLL_Impl_delete_last_in_dls(hp,
        k,
        (
          (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
            .tag = FStar_Pervasives_Native_None
          }
        ),
        concrete_tp);
    FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
    new_hd =
      fst__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(r);
    FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
    new_tl =
      snd__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node__FStar_Pervasives_Native_option__CLRS_Ch10_DLL_Impl_node_(r);
    *hd_ref = new_hd;
    *tl_ref = new_tl;
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

bool CLRS_Ch10_DLL_ImplTest_bool_eq(bool a, bool b)
{
  return a == b;
}

static bool
uu___is_Some___CLRS_Ch10_DLL_Impl_node_(
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ projectee
)
{
  if (projectee.tag == FStar_Pervasives_Native_Some)
    return true;
  else
    return false;
}

static bool
uu___is_None___CLRS_Ch10_DLL_Impl_node_(
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ projectee
)
{
  if (projectee.tag == FStar_Pervasives_Native_None)
    return true;
  else
    return false;
}

bool CLRS_Ch10_DLL_ImplTest_test_dll_spec_validation(void)
{
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
  hd_ref = { .tag = FStar_Pervasives_Native_None };
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
  tl_ref = { .tag = FStar_Pervasives_Native_None };
  list_insert(&hd_ref, &tl_ref, (krml_checked_int_t)3);
  list_insert(&hd_ref, &tl_ref, (krml_checked_int_t)2);
  list_insert(&hd_ref, &tl_ref, (krml_checked_int_t)1);
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd1 = hd_ref;
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ tl1 = tl_ref;
  bool found2 = list_search(hd1, (krml_checked_int_t)2);
  bool pass = found2 == true;
  bool not99 = list_search(hd1, (krml_checked_int_t)99);
  bool pass1 = pass && not99 == false;
  bool found3_back = list_search_back(hd1, tl1, (krml_checked_int_t)3);
  bool pass2 = pass1 && found3_back == true;
  bool not0_back = list_search_back(hd1, tl1, (krml_checked_int_t)0);
  bool pass3 = pass2 && not0_back == false;
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
  ptr1 = list_search_ptr(hd1, (krml_checked_int_t)1);
  bool pass4 = pass3 && uu___is_Some___CLRS_Ch10_DLL_Impl_node_(ptr1);
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_
  ptr42 = list_search_ptr(hd1, (krml_checked_int_t)42);
  bool pass5 = pass4 && uu___is_None___CLRS_Ch10_DLL_Impl_node_(ptr42);
  list_delete(&hd_ref, &tl_ref, (krml_checked_int_t)2);
  list_delete(&hd_ref, &tl_ref, (krml_checked_int_t)99);
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd2 = hd_ref;
  bool gone2 = list_search(hd2, (krml_checked_int_t)2);
  bool pass6 = pass5 && gone2 == false;
  bool still1 = list_search(hd2, (krml_checked_int_t)1);
  bool pass7 = pass6 && still1 == true;
  bool still3 = list_search(hd2, (krml_checked_int_t)3);
  bool pass8 = pass7 && still3 == true;
  list_delete(&hd_ref, &tl_ref, (krml_checked_int_t)1);
  list_delete(&hd_ref, &tl_ref, (krml_checked_int_t)3);
  hd_ref =
    (
      (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
        .tag = FStar_Pervasives_Native_None
      }
    );
  tl_ref =
    (
      (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
        .tag = FStar_Pervasives_Native_None
      }
    );
  list_insert(&hd_ref, &tl_ref, (krml_checked_int_t)10);
  list_insert_tail(&hd_ref, &tl_ref, (krml_checked_int_t)20);
  list_insert_tail(&hd_ref, &tl_ref, (krml_checked_int_t)30);
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd3 = hd_ref;
  bool f10 = list_search(hd3, (krml_checked_int_t)10);
  bool pass9 = pass8 && f10 == true;
  bool f20 = list_search(hd3, (krml_checked_int_t)20);
  bool pass10 = pass9 && f20 == true;
  bool f30 = list_search(hd3, (krml_checked_int_t)30);
  bool pass11 = pass10 && f30 == true;
  bool f99 = list_search(hd3, (krml_checked_int_t)99);
  bool pass12 = pass11 && f99 == false;
  list_delete(&hd_ref, &tl_ref, (krml_checked_int_t)10);
  list_delete(&hd_ref, &tl_ref, (krml_checked_int_t)20);
  list_delete(&hd_ref, &tl_ref, (krml_checked_int_t)30);
  hd_ref =
    (
      (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
        .tag = FStar_Pervasives_Native_None
      }
    );
  tl_ref =
    (
      (FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_){
        .tag = FStar_Pervasives_Native_None
      }
    );
  list_insert(&hd_ref, &tl_ref, (krml_checked_int_t)3);
  list_insert(&hd_ref, &tl_ref, (krml_checked_int_t)1);
  list_insert(&hd_ref, &tl_ref, (krml_checked_int_t)2);
  list_insert(&hd_ref, &tl_ref, (krml_checked_int_t)1);
  list_delete_last(&hd_ref, &tl_ref, (krml_checked_int_t)1);
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd4 = hd_ref;
  bool f1_s3 = list_search(hd4, (krml_checked_int_t)1);
  bool pass13 = pass12 && f1_s3 == true;
  bool f2_s3 = list_search(hd4, (krml_checked_int_t)2);
  bool pass14 = pass13 && f2_s3 == true;
  bool f3_s3 = list_search(hd4, (krml_checked_int_t)3);
  bool pass15 = pass14 && f3_s3 == true;
  list_delete_last(&hd_ref, &tl_ref, (krml_checked_int_t)99);
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd4b = hd_ref;
  bool f1_s3b = list_search(hd4b, (krml_checked_int_t)1);
  bool pass16 = pass15 && f1_s3b == true;
  list_delete(&hd_ref, &tl_ref, (krml_checked_int_t)1);
  list_delete(&hd_ref, &tl_ref, (krml_checked_int_t)2);
  list_delete(&hd_ref, &tl_ref, (krml_checked_int_t)3);
  list_insert(&hd_ref, &tl_ref, (krml_checked_int_t)30);
  list_insert(&hd_ref, &tl_ref, (krml_checked_int_t)20);
  list_insert(&hd_ref, &tl_ref, (krml_checked_int_t)10);
  list_delete_node(&hd_ref, &tl_ref, (krml_checked_int_t)1);
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd5 = hd_ref;
  bool f10_s4 = list_search(hd5, (krml_checked_int_t)10);
  bool pass17 = pass16 && f10_s4 == true;
  bool f30_s4 = list_search(hd5, (krml_checked_int_t)30);
  bool pass18 = pass17 && f30_s4 == true;
  bool f20_s4 = list_search(hd5, (krml_checked_int_t)20);
  bool pass19 = pass18 && f20_s4 == false;
  list_delete_node(&hd_ref, &tl_ref, (krml_checked_int_t)0);
  FStar_Pervasives_Native_option___CLRS_Ch10_DLL_Impl_node_ hd6 = hd_ref;
  bool f30_s4b = list_search(hd6, (krml_checked_int_t)30);
  bool pass20 = pass19 && f30_s4b == true;
  bool f10_s4b = list_search(hd6, (krml_checked_int_t)10);
  bool pass21 = pass20 && f10_s4b == false;
  list_delete_node(&hd_ref, &tl_ref, (krml_checked_int_t)0);
  return pass21;
}

