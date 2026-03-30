/* krml header omitted for test repeatability */


#include "CLRS_Ch10_Queue_ImplTest.h"

bool CLRS_Ch10_Queue_ImplTest_int_eq(krml_checked_int_t a, krml_checked_int_t b)
{
  return a == b;
}

bool CLRS_Ch10_Queue_ImplTest_bool_eq(bool a, bool b)
{
  return a == b;
}

typedef struct queue__krml_checked_int_t_s
{
  krml_checked_int_t *data;
  size_t *head;
  size_t *tail;
  size_t *size;
  size_t capacity_sz;
}
queue__krml_checked_int_t;

static queue__krml_checked_int_t
create_queue__krml_checked_int_t(krml_checked_int_t default_val, size_t capacity)
{
  KRML_CHECK_SIZE(sizeof (krml_checked_int_t), capacity);
  krml_checked_int_t *arr = KRML_HOST_MALLOC(sizeof (krml_checked_int_t) * capacity);
  if (arr != NULL)
    for (uint32_t _i = 0U; _i < capacity; ++_i)
      arr[_i] = default_val;
  size_t *head_ref = KRML_HOST_CALLOC(1U, sizeof (size_t));
  size_t *tail_ref = KRML_HOST_CALLOC(1U, sizeof (size_t));
  size_t *size_ref = KRML_HOST_CALLOC(1U, sizeof (size_t));
  return
    (
      (queue__krml_checked_int_t){
        .data = arr,
        .head = head_ref,
        .tail = tail_ref,
        .size = size_ref,
        .capacity_sz = capacity
      }
    );
}

static bool queue_empty__krml_checked_int_t(queue__krml_checked_int_t q)
{
  size_t size_val = *q.size;
  return size_val == (size_t)0U;
}

static void enqueue__krml_checked_int_t(queue__krml_checked_int_t q, krml_checked_int_t x)
{
  size_t tail_val = *q.tail;
  size_t size_val = *q.size;
  q.data[tail_val] = x;
  size_t new_tail_raw = tail_val + (size_t)1U;
  size_t cap_sz = q.capacity_sz;
  size_t new_tail = (size_t)0U;
  if (new_tail_raw >= cap_sz)
    new_tail = (size_t)0U;
  else
    new_tail = new_tail_raw;
  size_t new_tail_v = new_tail;
  size_t new_size = size_val + (size_t)1U;
  *q.tail = new_tail_v;
  *q.size = new_size;
}

static krml_checked_int_t dequeue__krml_checked_int_t(queue__krml_checked_int_t q)
{
  size_t head_val = *q.head;
  size_t size_val = *q.size;
  krml_checked_int_t elem = q.data[head_val];
  size_t new_head_raw = head_val + (size_t)1U;
  size_t cap_sz = q.capacity_sz;
  size_t new_head = (size_t)0U;
  if (new_head_raw >= cap_sz)
    new_head = (size_t)0U;
  else
    new_head = new_head_raw;
  size_t new_head_v = new_head;
  size_t new_size = size_val - (size_t)1U;
  *q.head = new_head_v;
  *q.size = new_size;
  return elem;
}

bool CLRS_Ch10_Queue_ImplTest_test_queue_spec_validation(void)
{
  queue__krml_checked_int_t
  q = create_queue__krml_checked_int_t((krml_checked_int_t)0, (size_t)5U);
  bool b0 = queue_empty__krml_checked_int_t(q);
  bool pass = b0 == true;
  enqueue__krml_checked_int_t(q, (krml_checked_int_t)10);
  enqueue__krml_checked_int_t(q, (krml_checked_int_t)20);
  enqueue__krml_checked_int_t(q, (krml_checked_int_t)30);
  bool b1 = queue_empty__krml_checked_int_t(q);
  bool pass1 = pass && b1 == false;
  krml_checked_int_t x1 = dequeue__krml_checked_int_t(q);
  bool pass2 = pass1 && x1 == (krml_checked_int_t)10;
  krml_checked_int_t x2 = dequeue__krml_checked_int_t(q);
  bool pass3 = pass2 && x2 == (krml_checked_int_t)20;
  krml_checked_int_t x3 = dequeue__krml_checked_int_t(q);
  bool pass4 = pass3 && x3 == (krml_checked_int_t)30;
  bool b2 = queue_empty__krml_checked_int_t(q);
  bool pass5 = pass4 && b2 == true;
  enqueue__krml_checked_int_t(q, (krml_checked_int_t)40);
  enqueue__krml_checked_int_t(q, (krml_checked_int_t)50);
  krml_checked_int_t y1 = dequeue__krml_checked_int_t(q);
  bool pass6 = pass5 && y1 == (krml_checked_int_t)40;
  enqueue__krml_checked_int_t(q, (krml_checked_int_t)60);
  krml_checked_int_t y2 = dequeue__krml_checked_int_t(q);
  bool pass7 = pass6 && y2 == (krml_checked_int_t)50;
  krml_checked_int_t y3 = dequeue__krml_checked_int_t(q);
  bool pass8 = pass7 && y3 == (krml_checked_int_t)60;
  bool b3 = queue_empty__krml_checked_int_t(q);
  return pass8 && b3 == true;
}

